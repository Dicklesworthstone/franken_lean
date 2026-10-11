//! Real candidate generation, retained Reference comparison, and admission by
//! both checking seats. Automatic source publication remains corpus-gated.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
use fln_core::expr::{BinderInfo, Expr, FVarId};
use fln_core::level::Level;
use fln_core::name::{LeafView, Name};
use fln_elab::inductive::auxiliaries::{AuxiliaryError, cases_on_declaration, rec_on_declaration};
use fln_elab::inductive::{ConstructorSpec, InductiveSpec, inductive_declaration};
use fln_elab::lctx::LocalDecl;
use fln_elab::records::RecordBudget;
use fln_env::constants::{ConstantInfo, DefinitionVal, InductiveVal, RecursorVal};
use fln_olean::decl::{ChainLimits, DeclDecoder, decode_chain_constants_from_parts};
use fln_olean::region::{OleanView, WalkBudget};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

fn name(s: &str) -> Name {
    Name::from_components(s.split('.'))
}

fn generation_budget() -> RecordBudget {
    RecordBudget {
        max_binders: 4096,
        max_nodes: 10_000_000,
    }
}

fn retained_prelude() -> &'static BTreeMap<Name, ConstantInfo> {
    static PRELUDE: OnceLock<BTreeMap<Name, ConstantInfo>> = OnceLock::new();
    PRELUDE.get_or_init(|| {
        let parts: [&[u8]; 3] = [
            include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean"),
            include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean.server"),
            include_bytes!("../../fln-conformance/fixtures/tag_attributes/prelude.olean.private"),
        ];
        decode_chain_constants_from_parts(parts[0], parts[1], parts[2], ChainLimits::default())
            .expect("the retained v4.32.0 Prelude chain decodes")
            .constants
            .into_iter()
            .map(|info| (info.name().clone(), info))
            .collect()
    })
}

fn recursor<'a>(constants: &'a BTreeMap<Name, ConstantInfo>, family: &Name) -> &'a RecursorVal {
    match constants.get(&Name::str(family.clone(), "rec")) {
        Some(ConstantInfo::Rec(rec)) => rec,
        other => panic!(
            "{} must have a recursor, got {other:?}",
            family.to_display_string()
        ),
    }
}

fn family<'a>(constants: &'a BTreeMap<Name, ConstantInfo>, n: &Name) -> &'a InductiveVal {
    match constants.get(n) {
        Some(ConstantInfo::Induct(ind)) => ind,
        other => panic!(
            "{} must be an inductive, got {other:?}",
            n.to_display_string()
        ),
    }
}

fn compare(actual: &DefinitionVal, expected: &DefinitionVal) -> Result<(), String> {
    if actual == expected {
        return Ok(());
    }
    Err(format!(
        "{}: type={}, value={}, universes={}, name={}, hints={}, safety={}, all={}",
        expected.base.name.to_display_string(),
        actual.base.type_ == expected.base.type_,
        actual.value == expected.value,
        actual.base.level_params == expected.base.level_params,
        actual.base.name == expected.base.name,
        actual.hints == expected.hints,
        actual.safety == expected.safety,
        actual.all == expected.all,
    ))
}

fn compare_module(constants: &BTreeMap<Name, ConstantInfo>) -> (usize, usize, Vec<String>) {
    let families: Vec<_> = constants
        .values()
        .filter_map(|info| match info {
            ConstantInfo::Induct(ind) => Some(ind.clone()),
            _ => None,
        })
        .collect();
    let mut rec_count = 0;
    let mut cases_count = 0;
    let mut mismatches = Vec::new();
    // Inventory actual definitions, so a suffix whose family has lost its
    // recursor cannot silently disappear from the tested population. A user
    // declaration in a namespace that is not an inductive is outside this gate.
    for info in constants.values() {
        let ConstantInfo::Defn(expected) = info else {
            continue;
        };
        let LeafView::Str(suffix @ ("recOn" | "casesOn")) = expected.base.name.leaf_view() else {
            continue;
        };
        let n = expected.base.name.parent();
        let Some(ConstantInfo::Induct(inductive)) = constants.get(&n) else {
            continue;
        };
        if suffix == "recOn" {
            rec_count += 1;
        } else {
            cases_count += 1;
        }
        let Some(ConstantInfo::Rec(rec)) = constants.get(&Name::str(n.clone(), "rec")) else {
            mismatches.push(format!(
                "{}: auxiliary definition has no family recursor",
                expected.base.name.to_display_string()
            ));
            continue;
        };
        let actual = if suffix == "recOn" {
            rec_on_declaration(rec, generation_budget())
        } else {
            cases_on_declaration(inductive, rec, &families, generation_budget())
        };
        match actual {
            Ok(actual) => {
                if let Err(error) = compare(&actual, expected) {
                    mismatches.push(error);
                }
            }
            Err(error) => mismatches.push(format!("{}.{}: {error}", n.to_display_string(), suffix)),
        }
    }
    (rec_count, cases_count, mismatches)
}

#[test]
fn reference_inventory_refuses_missing_family_recursors() {
    let constants: BTreeMap<_, _> = ["Nat", "Nat.recOn", "Nat.casesOn"]
        .into_iter()
        .map(|n| {
            let key = name(n);
            (key.clone(), retained_prelude()[&key].clone())
        })
        .collect();
    let (rec_count, cases_count, mismatches) = compare_module(&constants);
    assert_eq!((rec_count, cases_count), (1, 1));
    assert_eq!(
        mismatches.len(),
        2,
        "missing recursors do not skip candidates"
    );
}

#[test]
fn retained_reference_prelude_auxiliaries_are_exact_declarations() {
    let constants = retained_prelude();
    // These exercise recursion, parameterization, structures, indexed large
    // elimination, proposition elimination, and empty families respectively.
    for n in ["Nat", "List", "Prod", "Eq", "And", "False"] {
        let ind = family(constants, &name(n));
        recursor(constants, &ind.base.name);
        for suffix in ["recOn", "casesOn"] {
            assert!(
                matches!(
                    constants.get(&Name::str(name(n), suffix)),
                    Some(ConstantInfo::Defn(_))
                ),
                "{n}.{suffix}"
            );
        }
    }
    let (rec_count, cases_count, mismatches) = compare_module(constants);
    eprintln!(
        "retained Prelude: recOn={rec_count}, casesOn={cases_count}, mismatches={}",
        mismatches.len()
    );
    assert!(
        rec_count >= 10 && cases_count >= 10,
        "nonempty real auxiliary population"
    );
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));
}

fn admission_limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(8 * 1024 * 1024))
}

fn checked(engine: &Engine, source: &str) -> Engine {
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(admission_limits()),
        )
        .unwrap_or_else(|error| panic!("source {source}: {error:?}"))
        .into_complete()
        .expect("both seats return complete")
        .engine
}

fn install_auxiliaries(mut engine: Engine, names: &[&str]) -> Engine {
    let families: Vec<_> = names
        .iter()
        .map(|n| match engine.environment().find(&name(n)) {
            Some(ConstantInfo::Induct(ind)) => ind.clone(),
            other => panic!("missing family {n}: {other:?}"),
        })
        .collect();
    for ind in &families {
        let rec = match engine
            .environment()
            .find(&Name::str(ind.base.name.clone(), "rec"))
        {
            Some(ConstantInfo::Rec(rec)) => rec.clone(),
            _ => panic!("missing admitted recursor"),
        };
        let candidates = [
            rec_on_declaration(&rec, generation_budget()).unwrap(),
            cases_on_declaration(ind, &rec, &families, generation_budget()).unwrap(),
        ];
        for candidate in candidates {
            if let Some(existing) = engine.environment().find(&candidate.base.name) {
                let ConstantInfo::Defn(existing) = existing else {
                    panic!("a published auxiliary must be a definition");
                };
                assert_eq!(
                    existing, &candidate,
                    "ordinary source publication preserves the raw generator candidate"
                );
                continue;
            }
            engine = engine
                .admit_declaration(
                    fln::Declaration::Defn(candidate),
                    &KVMap::new(),
                    admission_limits(),
                )
                .expect("generated auxiliary reaches the ordinary two-seat admission")
                .into_complete()
                .expect("both seats accept the auxiliary")
                .engine;
        }
    }
    engine
}

#[test]
fn generated_case_analysis_and_recursion_compute_through_both_seats() {
    let engine = Engine::with_source_seed(admission_limits())
        .unwrap()
        .into_complete()
        .unwrap();
    // Deliberately enter through primitive candidate admission here. Ordinary
    // source now publishes auxiliary definitions itself; this still exercises
    // explicit independent admission of the raw generator's two candidates.
    let field = |s: &str, type_: Expr, index| LocalDecl {
        id: FVarId(name(s)),
        user_name: name(s),
        type_,
        value: None,
        binder_info: BinderInfo::Default,
        index,
    };
    let declaration = inductive_declaration(
        &InductiveSpec {
            name: name("Chain"),
            level_params: Vec::new(),
            parameters: Vec::new(),
            indices: Vec::new(),
            constructors: vec![
                ConstructorSpec {
                    name: name("nil"),
                    fields: Vec::new(),
                    result_indices: Vec::new(),
                },
                ConstructorSpec {
                    name: name("cons"),
                    fields: vec![
                        field("head", Expr::const_(name("Nat"), Vec::new()), 0),
                        field("tail", Expr::const_(name("Chain"), Vec::new()), 1),
                    ],
                    result_indices: Vec::new(),
                },
            ],
            result_level: Level::one(),
        },
        generation_budget(),
    )
    .unwrap();
    let engine = engine
        .admit_declaration(declaration, &KVMap::new(), admission_limits())
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    assert!(!engine.environment().contains(&name("Chain.casesOn")));
    assert!(!engine.environment().contains(&name("Chain.recOn")));
    let original = engine.logical_root(&KVMap::new());
    let generated = install_auxiliaries(engine.clone(), &["Chain"]);
    assert_eq!(
        engine.logical_root(&KVMap::new()),
        original,
        "candidate generation preserves the base snapshot"
    );
    checked(
        &generated,
        "theorem chain_case : @Chain.casesOn (fun _ => Nat) (Chain.cons 7 Chain.nil) 0 (fun head tail => head) = 7 := by rfl\n\
         theorem chain_rec : @Chain.recOn (fun _ => Nat) (Chain.cons 7 Chain.nil) 0 (fun head tail ih => ih + 1) = 1 := by rfl",
    );
    assert!(generated.check_source_files(
        &[b"theorem bad_case : @Chain.casesOn (fun _ => Nat) (Chain.cons 7 Chain.nil) 0 (fun head tail => head) = 8 := by rfl"],
        &KVMap::new(), SourceCheckLimits::new(admission_limits())
    ).is_err(), "wrong branch result is not a proof");
}

#[test]
fn generated_mutual_cases_drop_only_induction_hypotheses() {
    let engine = Engine::with_source_seed(admission_limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let engine = checked(
        &engine,
        "mutual\ninductive Tree where | node (forest : Forest)\ninductive Forest where | nil | cons (tree : Tree) (rest : Forest)\nend",
    );
    // The admitted seed supplies PUnit for the discarded sibling motive.
    assert!(engine.environment().contains(&name("PUnit")));
    let generated = install_auxiliaries(engine, &["Tree", "Forest"]);
    checked(
        &generated,
        "theorem tree_case : @Tree.casesOn (fun _ => Nat) (Tree.node Forest.nil) (fun children => 11) = 11 := by rfl\n\
         theorem forest_case : @Forest.casesOn (fun _ => Nat) (Forest.cons (Tree.node Forest.nil) Forest.nil) 0 (fun tree rest => 13) = 13 := by rfl",
    );
}

#[test]
fn indexed_and_function_recursive_auxiliaries_keep_dependent_arguments() {
    let engine = Engine::with_source_seed(admission_limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let engine = checked(
        &engine,
        "inductive Vec (A : Type) : Nat -> Type where\n\
         | nil : Vec A 0\n\
         | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n\
         inductive Branch where | leaf (n : Nat) | node (next : Nat -> Branch)",
    );
    let generated = install_auxiliaries(engine, &["Vec", "Branch"]);
    checked(
        &generated,
        "theorem vec_case : @Vec.casesOn Nat (fun n _ => Nat) (Nat.succ 0) (@Vec.cons Nat 0 7 (@Vec.nil Nat)) 0 (fun n head tail => head) = 7 := by rfl\n\
         theorem vec_rec : @Vec.recOn Nat (fun n _ => Nat) (Nat.succ 0) (@Vec.cons Nat 0 7 (@Vec.nil Nat)) 0 (fun n head tail ih => ih + 1) = 1 := by rfl\n\
         theorem branch_case : @Branch.casesOn (fun _ => Nat) (Branch.node (fun _ => Branch.leaf 2)) (fun n => n) (fun next => 17) = 17 := by rfl\n\
         theorem branch_rec : @Branch.recOn (fun _ => Nat) (Branch.node (fun _ => Branch.leaf 2)) (fun n => n) (fun next ih => ih 0 + 1) = 3 := by rfl",
    );
}

#[test]
fn malformed_metadata_and_generation_exhaustion_are_typed_non_candidates() {
    let constants = retained_prelude();
    let rec = recursor(constants, &name("Nat"));
    let ind = family(constants, &name("Nat"));
    let mut wrong = rec.clone();
    wrong.num_indices += 1;
    assert_eq!(
        rec_on_declaration(&wrong, generation_budget()),
        Err(AuxiliaryError::InvalidTelescope)
    );
    assert_eq!(
        cases_on_declaration(ind, &wrong, std::slice::from_ref(ind), generation_budget()),
        Err(AuxiliaryError::InconsistentFamily)
    );
    let mut wrong = rec.clone();
    wrong.base.name = name("Nat.notARecursor");
    assert_eq!(
        rec_on_declaration(&wrong, generation_budget()),
        Err(AuxiliaryError::InvalidRecursorName)
    );
    assert_eq!(
        cases_on_declaration(ind, rec, &[], generation_budget()),
        Err(AuxiliaryError::InconsistentFamily)
    );
    for budget in [
        RecordBudget {
            max_binders: 0,
            max_nodes: 10000,
        },
        RecordBudget {
            max_binders: 256,
            max_nodes: 0,
        },
    ] {
        assert_eq!(
            rec_on_declaration(rec, budget),
            Err(AuxiliaryError::ResourceLimit)
        );
        assert_eq!(
            cases_on_declaration(ind, rec, std::slice::from_ref(ind), budget),
            Err(AuxiliaryError::ResourceLimit)
        );
    }
}

fn collect_olean_paths(root: &Path, files: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(root)
        .unwrap()
        .map(|entry| entry.unwrap())
        .collect();
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let kind = entry.file_type().unwrap();
        if kind.is_dir() {
            collect_olean_paths(&entry.path(), files);
        } else if kind.is_file() && entry.path().extension().is_some_and(|ext| ext == "olean") {
            files.push(entry.path());
        }
    }
}

#[test]
fn pinned_stdlib_auxiliary_identity_frontier() {
    let Some(root) = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "FLN_REQUIRE_REFERENCE needs FLN_REFERENCE_LIB for the whole-stdlib generator gate"
        );
        eprintln!(
            "SKIP: pinned stdlib auxiliary frontier requires FLN_REFERENCE_LIB; retained Prelude comparisons still run"
        );
        return;
    };
    let mut files = Vec::new();
    collect_olean_paths(&root, &mut files);
    assert!(
        files.len() >= 2000,
        "whole-stdlib gate cannot be satisfied by a fixture subset"
    );
    let mut rec_count = 0;
    let mut cases_count = 0;
    let mut mismatches = Vec::new();
    for path in &files {
        let exported = std::fs::read(path).unwrap();
        let constants = if path.with_extension("olean.private").is_file() {
            decode_chain_constants_from_parts(
                &exported,
                &std::fs::read(path.with_extension("olean.server")).unwrap(),
                &std::fs::read(path.with_extension("olean.private")).unwrap(),
                ChainLimits::default(),
            )
            .unwrap_or_else(|error| panic!("{}: {error}", path.display()))
            .constants
        } else {
            let view = OleanView::parse(&exported).unwrap();
            DeclDecoder::new(&view, WalkBudget::default())
                .decode_module_constants()
                .unwrap()
        };
        let constants = constants
            .into_iter()
            .map(|info| (info.name().clone(), info))
            .collect();
        let (recs, cases, errors) = compare_module(&constants);
        rec_count += recs;
        cases_count += cases;
        mismatches.extend(
            errors
                .into_iter()
                .map(|error| format!("{}: {error}", path.display())),
        );
    }
    eprintln!(
        "pinned stdlib: modules={}, recOn={rec_count}, casesOn={cases_count}, mismatches={}",
        files.len(),
        mismatches.len()
    );
    assert!(
        rec_count >= 100 && cases_count >= 100,
        "generator population must cover real stdlib families"
    );
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));
}
