//! Integer branching is an explicit Frontier capability. All successful source
//! proofs and persisted products still pass both ordinary checker seats.
#![forbid(unsafe_code)]
use super::{assert_cases_complete, import_closure_in_mode, limits, n, record_case};
use fln::source_check::modules::persisted::{
    ModuleDecision, ModuleRecordLookup, ModuleRecordWrite, PersistedModules, SourceModuleKey,
    SourceModuleStore,
};
use fln::source_check::modules::reuse::CheckerIdentity;
use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession,
};
use fln::{Engine, KVMap, Mode, OleanWriteBudget, Outcome, SourceCheckLimits, SourceModuleInput};
use fln_core::outcome::InconclusiveCause;
use fln_elab::NatDefinitionElabError;
use fln_elab::arithmetic::{
    ArithmeticProvider, LinearConstraint, OmegaBranchNode, OmegaInconclusive, OmegaLimits,
    OmegaOutcome, OmegaResource, OmegaStep,
};
use fln_elab::source::SourceInferenceError;
use fln_elab::source::scope::SourceScope;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::path::Path;

// Live v4.32.0 omega refuses this integer-infeasible, rationally feasible system.
// Reordering Nat hypotheses also changes the pin's elimination order: bounds
// or the Nat type alone cannot justify enabling a stronger faithful solver.
const INTEGER_GAP: &str = "theorem integerGap (x y : Int) (hy : 0 ≤ y) (h₁ : 5*x ≤ 7+2*y) (h₂ : 5+5*y ≤ 4*x) : False := by omega";
const COIN_BOUNDARY: &str = "theorem branchBoundary (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : 2*x+3*y=1) : False := by\n  try omega";
const RECOVERY: &str = "theorem integerSearchRecovery (n : Nat) : n < n + 1 := by omega";

fn engine_in_mode(base: &Engine, mode: Mode) -> Engine {
    Engine::builder()
        .mode(mode)
        .build_from_environment(base.environment().clone())
}

fn checked(base: &Engine, source: &str, name: &str) {
    let before = base.logical_root(&KVMap::new());
    let result = base
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{name}: {error:?}"))
        .into_complete()
        .unwrap_or_else(|reason| panic!("{name}: incomplete proof: {reason:?}"));
    assert!(result.engine.environment().contains(&n(name)), "{name}");
    assert_eq!(result.engine.mode(), base.mode());
    assert_eq!(base.logical_root(&KVMap::new()), before);
}

fn integer_search_required<T: std::fmt::Debug, E: std::fmt::Debug>(result: Result<Outcome<T>, E>) {
    let result = result.expect("missing integer search stays a typed nonanswer");
    let Outcome::Inconclusive(reason) = result else {
        panic!("faithful elimination must not acquire frontier coverage: {result:?}");
    };
    assert!(
        matches!(&reason.cause, InconclusiveCause::Unsupported { construct }
            if construct.text() == "omega integer residue elimination"),
        "the expected integer-search gap, not resource exhaustion: {reason:?}"
    );
}

pub(super) fn assert_proofs(base: &Engine) {
    let frontier = engine_in_mode(base, Mode::Frontier);
    let mut failures = Vec::new();
    for (name, source) in [
        ("integerGap", INTEGER_GAP),
        (
            "naturalGap",
            "theorem naturalGap (x y : Nat) (h₁ : 5*x ≤ 7+2*y) (h₂ : 5+5*y ≤ 4*x) : False := by omega",
        ),
        (
            "naturalGapReordered",
            "theorem naturalGapReordered (x y : Nat) (h₂ : 5+5*y ≤ 4*x) (h₁ : 5*x ≤ 7+2*y) : False := by omega",
        ),
        (
            "integerBoundsReordered",
            "theorem integerBoundsReordered (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) (h₁ : 5*x ≤ 7+2*y) (h₂ : 5+5*y ≤ 4*x) : False := by omega",
        ),
        (
            "negativeIntegerGap",
            "theorem negativeIntegerGap (x y : Int) (hy : 0 ≤ y) (h₁ : -7-2*y ≤ 5*x) (h₂ : 4*x ≤ -5-5*y) : False := by omega",
        ),
        (
            "nonnegativeCoinGap",
            "theorem nonnegativeCoinGap (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : 2*x+3*y=1) : False := by omega",
        ),
        (
            "quotientIntegerGap",
            "theorem quotientIntegerGap (x n : Int) (hy : 0 ≤ n / 7) (h₁ : 5*x ≤ 7+2*(n / 7)) (h₂ : 5+5*(n / 7) ≤ 4*x) : False := by omega",
        ),
    ] {
        record_case(&mut failures, name, || checked(&frontier, source, name));
    }
    for mode in [Mode::Sound, Mode::Faithful] {
        record_case(&mut failures, &format!("{mode:?} isolation"), || {
            let engine = engine_in_mode(base, mode);
            let before = engine.logical_root(&KVMap::new());
            integer_search_required(engine.check_source_files(
                &[INTEGER_GAP.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            ));
            assert!(!engine.environment().contains(&n("integerGap")));
            assert_eq!(engine.logical_root(&KVMap::new()), before);
            checked(&engine, RECOVERY, "integerSearchRecovery");
        });
    }
    // Known witnesses distinguish failed proof search from integer UNSAT.
    // They are respectively (-1, 1), (1, 0), and (-1, 0).
    for source in [
        "theorem satisfiableCoin (x y : Int) (h : 2*x+3*y=1) : False := by omega",
        "theorem relaxedNaturalGap (x y : Nat) (h₁ : 5*x ≤ 7+2*y) (h₂ : 4+5*y ≤ 4*x) : False := by omega",
        "theorem relaxedNegativeGap (x y : Int) (hy : 0 ≤ y) (h₁ : -7-2*y ≤ 5*x) (h₂ : 4*x ≤ -4-5*y) : False := by omega",
    ] {
        record_case(&mut failures, source, || {
            let before = frontier.logical_root(&KVMap::new());
            let refusal = frontier
                .check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits()),
                )
                .expect_err("a satisfiable integer system cannot close False");
            assert!(
                refusal
                    .to_string()
                    .contains("omega could not prove the goal"),
                "{refusal:?}"
            );
            assert_eq!(frontier.logical_root(&KVMap::new()), before);
        });
    }
    record_case(&mut failures, "frontier recovery", || {
        checked(&frontier, RECOVERY, "integerSearchRecovery");
    });
    assert_cases_complete(&failures);
}

type Provider = fn(&[LinearConstraint], OmegaLimits) -> OmegaOutcome;

fn genuine_branches(inputs: &[LinearConstraint], limits: OmegaLimits) -> OmegaOutcome {
    let result = fln_anvil::omega::solve_with_integer_search(inputs, limits);
    let OmegaOutcome::UnsatBranches { certificate, .. } = &result else {
        panic!("the real reified fixture must require integer branches: {result:?}");
    };
    assert!(
        certificate
            .nodes
            .iter()
            .any(|node| matches!(node, OmegaBranchNode::Split { .. }))
    );
    fln_anvil::omega::check_branch_certificate(inputs, certificate, limits)
        .expect("the provider's ordinary numeric certificate is valid");
    result
}

fn corrupted<const KIND: u8>(inputs: &[LinearConstraint], limits: OmegaLimits) -> OmegaOutcome {
    let OmegaOutcome::UnsatBranches {
        mut certificate,
        steps_used,
    } = genuine_branches(inputs, limits)
    else {
        unreachable!()
    };
    match KIND {
        0 => certificate.inputs.swap(0, 1),
        1 => {
            let leaf = certificate
                .nodes
                .iter_mut()
                .find_map(|node| match node {
                    OmegaBranchNode::Leaf { certificate } => Some(certificate),
                    _ => None,
                })
                .unwrap();
            assert!(leaf.inputs.len() > inputs.len());
            leaf.inputs.pop();
        }
        2 => {
            let leaf = certificate
                .nodes
                .iter_mut()
                .find_map(|node| match node {
                    OmegaBranchNode::Leaf { certificate }
                        if certificate.inputs.len() >= inputs.len() + 2 =>
                    {
                        Some(certificate)
                    }
                    _ => None,
                })
                .expect("the coin gap has nested branch assumptions");
            let len = leaf.inputs.len();
            leaf.inputs.swap(len - 1, len - 2);
        }
        3 | 4 => {
            let OmegaBranchNode::Split { le, gt, .. } = certificate.nodes.last_mut().unwrap()
            else {
                unreachable!()
            };
            if KIND == 3 {
                std::mem::swap(le, gt);
            } else {
                *gt = *le;
            }
        }
        5 => {
            // Insert a disconnected leaf while preserving every old edge.
            let dead = certificate.nodes[0].clone();
            for node in &mut certificate.nodes {
                if let OmegaBranchNode::Split { le, gt, .. } = node {
                    *le += 1;
                    *gt += 1;
                }
            }
            certificate.nodes.insert(0, dead);
            certificate.conclusion += 1;
        }
        6 => certificate.version += 1,
        _ => unreachable!(),
    }
    OmegaOutcome::UnsatBranches {
        certificate,
        steps_used,
    }
}

fn cancelled_search(inputs: &[LinearConstraint], limits: OmegaLimits) -> OmegaOutcome {
    // Cancel at the last metered operation of an otherwise successful search,
    // after rational reconstruction and real branch work have already happened.
    let mut total_polls = 0;
    let complete =
        fln_anvil::omega::solve_with_integer_search_and_cancel(inputs, limits, &mut || {
            total_polls += 1;
            false
        });
    assert!(matches!(complete, OmegaOutcome::UnsatBranches { .. }));
    let mut polls = 0;
    let result =
        fln_anvil::omega::solve_with_integer_search_and_cancel(inputs, limits, &mut || {
            polls += 1;
            polls >= total_polls
        });
    assert!(
        matches!(result, OmegaOutcome::Inconclusive { reason: OmegaInconclusive::Cancelled, steps_used } if steps_used > 0)
    );
    result
}

fn exhausted_search(inputs: &[LinearConstraint], mut limits: OmegaLimits) -> OmegaOutcome {
    let OmegaOutcome::UnsatBranches { steps_used, .. } = genuine_branches(inputs, limits) else {
        unreachable!()
    };
    limits.max_steps = steps_used - 1;
    let result = fln_anvil::omega::solve_with_integer_search(inputs, limits);
    assert!(
        matches!(result, OmegaOutcome::Inconclusive { reason: OmegaInconclusive::ResourceLimit { resource: OmegaResource::Steps, limit, observed }, .. } if observed > limit)
    );
    result
}

fn expanded_branches(inputs: &[LinearConstraint], limits: OmegaLimits) -> OmegaOutcome {
    let OmegaOutcome::UnsatBranches {
        mut certificate,
        steps_used,
    } = genuine_branches(inputs, limits)
    else {
        unreachable!()
    };
    let one = inputs
        .iter()
        .flat_map(|row| &row.coeffs)
        .map(|coefficient| coefficient.magnitude())
        .find(|magnitude| magnitude.limbs_le() == [1])
        .unwrap()
        .clone();
    let leaves = certificate
        .nodes
        .iter()
        .filter(|node| matches!(node, OmegaBranchNode::Leaf { .. }))
        .count();
    assert!(leaves > 1);
    // Each leaf fits separately. Only cumulative proof accounting across the
    // tree stops this valid certificate, as required even with source fuel left.
    let extra = (usize::try_from(limits.max_steps.div_ceil(224)).unwrap() + 32).div_ceil(leaves);
    for node in &mut certificate.nodes {
        if let OmegaBranchNode::Leaf { certificate } = node {
            for _ in 0..extra {
                let parent = certificate.conclusion;
                certificate.steps.push(OmegaStep::Combine {
                    left: parent,
                    right: parent,
                    left_scale: one.clone(),
                    right_scale: one.clone(),
                });
                certificate.conclusion = u32::try_from(certificate.steps.len() - 1).unwrap();
            }
        }
    }
    fln_anvil::omega::check_branch_certificate(inputs, &certificate, limits)
        .expect("expanded branches remain numerically valid within checker limits");
    // Preserve actual solver work: the stop must come from source proof replay.
    OmegaOutcome::UnsatBranches {
        certificate,
        steps_used,
    }
}

pub(super) fn assert_provider_boundary(base: &Engine) {
    let engine = engine_in_mode(base, Mode::Frontier);
    let before = engine.logical_root(&KVMap::new());
    let parsed =
        fln_parse::parse_definition(COIN_BOUNDARY.as_bytes()).expect("branch source parses");
    let elaborate = |provider: Provider| {
        fln_elab::elaborate_definition_in_scope_with_budget(
            parsed.syntax(),
            engine.environment(),
            limits().kernel,
            &SourceScope {
                arithmetic: Some(ArithmeticProvider(provider)),
                frontier_recursors: true,
                ..SourceScope::default()
            },
        )
    };
    let mut failures = Vec::new();
    for (label, provider) in [
        ("root inputs", corrupted::<0> as Provider),
        ("missing path assumption", corrupted::<1>),
        ("reordered path", corrupted::<2>),
        ("swapped siblings", corrupted::<3>),
        ("shared child", corrupted::<4>),
        ("dead node", corrupted::<5>),
        ("branch version", corrupted::<6>),
    ] {
        record_case(&mut failures, label, || {
            match elaborate(provider) {
                Err(NatDefinitionElabError::Inference(SourceInferenceError::Tactic(reason))) => {
                    assert_eq!(
                        reason.to_string(),
                        "native arithmetic returned an invalid certificate"
                    );
                }
                result => panic!("{label}: certificate corruption must escape try: {result:?}"),
            }
            assert_eq!(engine.logical_root(&KVMap::new()), before);
        });
    }
    for (label, provider) in [
        ("branch cancellation", cancelled_search as Provider),
        ("branch search budget", exhausted_search),
        ("cumulative branch proof budget", expanded_branches),
    ] {
        record_case(&mut failures, label, || {
            match elaborate(provider) {
                Err(NatDefinitionElabError::Inference(
                    SourceInferenceError::ArithmeticInconclusive(reason),
                )) => {
                    if label == "branch cancellation" {
                        assert!(matches!(reason.cause, InconclusiveCause::Cancelled { .. }));
                    } else {
                        assert!(
                            matches!(reason.cause, InconclusiveCause::ResourceExhausted { usage } if usage.is_genuine_exhaustion())
                        );
                    }
                }
                Err(NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit))
                    if label == "cumulative branch proof budget" => {}
                result => panic!("{label}: the typed stop must escape try: {result:?}"),
            }
            assert_eq!(engine.logical_root(&KVMap::new()), before);
        });
    }
    record_case(&mut failures, "real branch proof and recovery", || {
        let declaration = elaborate(genuine_branches)
            .expect("a restored real provider produces a closed branch proof");
        let admitted = engine
            .admit_declaration(declaration, &KVMap::new(), limits())
            .expect("the branch proof crosses ordinary dual admission")
            .into_complete()
            .expect("both checker seats accept the branch proof");
        assert!(admitted.engine.environment().contains(&n("branchBoundary")));
        assert_eq!(engine.logical_root(&KVMap::new()), before);
        checked(&engine, RECOVERY, "integerSearchRecovery");
    });
    assert_cases_complete(&failures);
}

pub(super) fn assert_scoped_proofs(base: &Engine) {
    let engine = engine_in_mode(base, Mode::Frontier);
    let scoped = format!(
        "namespace IntegerScope\nsection\n{INTEGER_GAP}\nend\nend IntegerScope\n{INTEGER_GAP}"
    );
    let next = "theorem nextIntegerFile (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : 2*x+3*y=1) : False := by omega";
    let checked = engine
        .check_source_files(
            &[scoped.as_bytes(), next.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .expect("integer search survives namespace, section, and file restoration")
        .into_complete()
        .expect("every scoped branch proof passes both seats");
    assert_eq!(checked.theorems, 3);
    for name in ["IntegerScope.integerGap", "integerGap", "nextIntegerFile"] {
        assert!(checked.engine.environment().contains(&n(name)), "{name}");
    }
    assert_eq!(checked.engine.mode(), Mode::Frontier);
    assert_eq!(
        checked.scope.arithmetic,
        Some(ArithmeticProvider(
            fln_anvil::omega::solve_with_integer_search
        ))
    );
}

#[derive(Default)]
struct Records {
    values: RefCell<BTreeMap<SourceModuleKey, Vec<u8>>>,
    lookups: RefCell<Vec<(SourceModuleKey, bool)>>,
}

impl SourceModuleStore for Records {
    fn load(&self, key: SourceModuleKey) -> Result<Option<Vec<u8>>, String> {
        let value = self.values.borrow().get(&key).cloned();
        self.lookups.borrow_mut().push((key, value.is_some()));
        Ok(value)
    }

    fn save(&self, key: SourceModuleKey, bytes: &[u8]) -> Result<(), String> {
        self.values.borrow_mut().insert(key, bytes.to_vec());
        Ok(())
    }
}

fn session(base: &Engine) -> SourceModuleSession {
    SourceModuleSession::new(
        base.clone(),
        KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        SourceModuleCacheLimits::default(),
    )
}

pub(super) fn assert_module_replay(base: &Engine, lib: &Path) {
    // A real import receipt is required for artifact compilation. Cloning only
    // Environment would erase that authority and correctly yield UnboundBase.
    let frontier = import_closure_in_mode(lib, Mode::Frontier);
    let library = format!("prelude\nimport Init.Omega\n{INTEGER_GAP}");
    let client = "prelude\nimport IntegerLibrary\ntheorem moduleCoinGap (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : 2*x+3*y=1) : False := by omega";
    let names = [n("IntegerLibrary"), n("IntegerClient")];
    let inputs = [
        SourceModuleInput {
            name: &names[0],
            source: library.as_bytes(),
        },
        SourceModuleInput {
            name: &names[1],
            source: client.as_bytes(),
        },
    ];
    let records = Records::default();
    let persisted = PersistedModules {
        checker: CheckerIdentity::of_executable(b"native-integer-branch-source-gate"),
        store: &records,
    };
    let mut retained = session(&frontier);
    let cold = retained
        .compile_with_records(
            &inputs,
            &names[1],
            OleanWriteBudget::default(),
            Some(persisted),
            None,
        )
        .expect("cold frontier module compilation")
        .into_complete()
        .expect("cold branch modules pass both seats");
    assert_eq!(
        (
            cold.elaborated_modules,
            cold.persisted_modules,
            cold.reused_modules
        ),
        (2, 0, 0)
    );
    assert!(
        cold.modules
            .iter()
            .all(|row| row.record == ModuleRecordLookup::Absent
                && row.record_write == ModuleRecordWrite::Stored)
    );
    let retained_warm = retained
        .compile(&inputs, &names[1], OleanWriteBudget::default())
        .expect("retained frontier module compilation")
        .into_complete()
        .expect("retained branch modules complete");
    assert_eq!(
        (
            retained_warm.reused_modules,
            retained_warm.elaborated_modules
        ),
        (2, 0)
    );
    let warm = session(&frontier)
        .compile_with_records(
            &inputs,
            &names[1],
            OleanWriteBudget::default(),
            Some(persisted),
            None,
        )
        .expect("fresh-session frontier record replay")
        .into_complete()
        .expect("persisted branch proofs are re-admitted by both seats");
    assert_eq!((warm.elaborated_modules, warm.persisted_modules), (0, 2));
    assert!(
        warm.modules
            .iter()
            .all(|row| row.decision == ModuleDecision::Cached
                && row.record == ModuleRecordLookup::Hit)
    );
    for replay in [&retained_warm, &warm] {
        assert_eq!(
            cold.checked.checked.engine.logical_root(&KVMap::new()),
            replay.checked.checked.engine.logical_root(&KVMap::new())
        );
        assert_eq!(cold.artifacts.len(), replay.artifacts.len());
        for (cold, warm) in cold.artifacts.iter().zip(&replay.artifacts) {
            assert_eq!(cold.name, warm.name);
            assert_eq!(cold.bytes, warm.bytes);
        }
        checked(
            &replay.checked.checked.engine,
            "theorem afterModuleReplay (x y : Int) (hy : 0 ≤ y) (h₁ : 5*x ≤ 7+2*y) (h₂ : 5+5*y ≤ 4*x) : False := by omega",
            "afterModuleReplay",
        );
    }
    for mode in [Mode::Sound, Mode::Faithful] {
        // Reuse the original checked Sound receipt; only Faithful needs its own
        // import. No test-only mode setter can bless an unbound environment.
        let faithful;
        let engine = if mode == Mode::Sound {
            base
        } else {
            faithful = import_closure_in_mode(lib, mode);
            &faithful
        };
        records.lookups.borrow_mut().clear();
        let prior_records = records.values.borrow().len();
        integer_search_required(session(engine).compile_with_records(
            &inputs,
            &names[1],
            OleanWriteBudget::default(),
            Some(persisted),
            None,
        ));
        let lookups = records.lookups.borrow();
        assert_eq!(lookups.len(), 1, "the first source module is re-elaborated");
        assert!(
            !lookups[0].1,
            "a frontier record cannot answer another mode's lookup"
        );
        assert_ne!(Some(lookups[0].0), cold.modules[0].key);
        assert_eq!(
            records.values.borrow().len(),
            prior_records,
            "nonanswers write no module records"
        );
        checked(engine, RECOVERY, "integerSearchRecovery");
    }
}
