//! Native course-of-values candidates, exact pinned definitions, two-seat
//! admission, and recursive computation in proofs about a user-declared family.
#![forbid(unsafe_code)]

use fln::{Budget, Declaration, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
use fln_core::expr::{Expr, ExprNode};
use fln_core::name::{LeafView, Name};
use fln_elab::inductive::auxiliaries::{AuxiliaryError, below_declaration, brec_on_declarations};
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
        max_binders: 16_384,
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
            .unwrap()
            .constants
            .into_iter()
            .map(|info| (info.name().clone(), info))
            .collect()
    })
}

fn families(constants: &BTreeMap<Name, ConstantInfo>) -> Vec<InductiveVal> {
    constants
        .values()
        .filter_map(|info| match info {
            ConstantInfo::Induct(ind) => Some(ind.clone()),
            _ => None,
        })
        .collect()
}

fn recursor<'a>(constants: &'a BTreeMap<Name, ConstantInfo>, n: &str) -> &'a RecursorVal {
    let Some(ConstantInfo::Rec(rec)) = constants.get(&name(n)) else {
        panic!("missing recursor {n}")
    };
    rec
}

fn first_difference(actual: &Expr, expected: &Expr) -> String {
    let mut work = vec![(actual, expected, String::new())];
    while let Some((a, b, path)) = work.pop() {
        if a == b {
            continue;
        }
        match (a.node(), b.node()) {
            (ExprNode::App { f: af, a: aa }, ExprNode::App { f: bf, a: ba }) => {
                work.push((aa, ba, format!("{path}.arg")));
                work.push((af, bf, format!("{path}.fn")));
            }
            (
                ExprNode::Lam {
                    binder_type: at,
                    body: ab,
                    ..
                }
                | ExprNode::ForallE {
                    binder_type: at,
                    body: ab,
                    ..
                },
                ExprNode::Lam {
                    binder_type: bt,
                    body: bb,
                    ..
                }
                | ExprNode::ForallE {
                    binder_type: bt,
                    body: bb,
                    ..
                },
            ) => {
                work.push((ab, bb, format!("{path}.body")));
                work.push((at, bt, format!("{path}.domain")));
            }
            _ => return format!("{path}: actual={a:?}; expected={b:?}"),
        }
    }
    "binder annotation or expression metadata differs".into()
}

fn compare(actual: &DefinitionVal, expected: &DefinitionVal) -> Result<(), String> {
    if actual == expected {
        return Ok(());
    }
    let detail = if actual.base.type_ != expected.base.type_ {
        first_difference(&actual.base.type_, &expected.base.type_)
    } else if actual.value != expected.value {
        first_difference(&actual.value, &expected.value)
    } else {
        "non-expression declaration metadata differs".into()
    };
    Err(format!(
        "{}: type={}, value={}, universes={}, hints={}, safety={}, all={}; {detail}",
        expected.base.name.to_display_string(),
        actual.base.type_ == expected.base.type_,
        actual.value == expected.value,
        actual.base.level_params == expected.base.level_params,
        actual.hints == expected.hints,
        actual.safety == expected.safety,
        actual.all == expected.all,
    ))
}

struct Candidate {
    recursor: RecursorVal,
    below: DefinitionVal,
    go: DefinitionVal,
    brec: DefinitionVal,
}

fn inventory(constants: &BTreeMap<Name, ConstantInfo>) -> Vec<Candidate> {
    let mut candidates = Vec::new();
    // Inventory the actual generated definitions, so dropping a recursor
    // cannot silently shrink the tested population.
    for info in constants.values() {
        let ConstantInfo::Defn(below) = info else {
            continue;
        };
        let LeafView::Str(suffix) = below.base.name.leaf_view() else {
            continue;
        };
        let Some(index) = suffix.strip_prefix("below") else {
            continue;
        };
        if !index.is_empty()
            && index
                .strip_prefix('_')
                .and_then(|s| s.parse::<u32>().ok())
                .is_none()
        {
            continue;
        }
        let owner = below.base.name.parent();
        if !matches!(constants.get(&owner), Some(ConstantInfo::Induct(_))) {
            continue;
        }
        let Some(ConstantInfo::Rec(rec)) =
            constants.get(&Name::str(owner.clone(), format!("rec{index}")))
        else {
            panic!(
                "{} has no matching family recursor",
                below.base.name.to_display_string()
            )
        };
        let brec_name = Name::str(owner, format!("brecOn{index}"));
        let Some(ConstantInfo::Defn(brec)) = constants.get(&brec_name) else {
            panic!("missing {}", brec_name.to_display_string())
        };
        let Some(ConstantInfo::Defn(go)) = constants.get(&Name::str(brec_name, "go")) else {
            panic!("missing course-of-values helper")
        };
        candidates.push(Candidate {
            recursor: rec.clone(),
            below: below.clone(),
            go: go.clone(),
            brec: brec.clone(),
        });
    }
    candidates
}

fn compare_candidates(candidates: &[Candidate], families: &[InductiveVal]) -> Vec<String> {
    let mut errors = Vec::new();
    for candidate in candidates {
        let below = below_declaration(&candidate.recursor, families, generation_budget());
        match below {
            Ok(actual) => {
                if let Err(error) = compare(&actual, &candidate.below) {
                    errors.push(error);
                }
            }
            Err(error) => errors.push(format!(
                "{}: {error}",
                candidate.below.base.name.to_display_string()
            )),
        }
        let brec = brec_on_declarations(&candidate.recursor, families, generation_budget());
        match brec {
            Ok([go, brec]) => {
                for (actual, expected) in [(&go, &candidate.go), (&brec, &candidate.brec)] {
                    if let Err(error) = compare(actual, expected) {
                        errors.push(error);
                    }
                }
            }
            Err(error) => errors.push(format!(
                "{}: {error}",
                candidate.brec.base.name.to_display_string()
            )),
        }
    }
    errors
}

#[test]
fn retained_reference_course_of_values_definitions_are_exact() {
    let constants = retained_prelude();
    let candidates = inventory(constants);
    assert!(
        candidates.len() >= 3,
        "the retained fixture includes Nat, List and Name"
    );
    let errors = compare_candidates(&candidates, &families(constants));
    eprintln!(
        "retained Prelude course-of-values: families={}, definitions={}, mismatches={}",
        candidates.len(),
        candidates.len() * 3,
        errors.len()
    );
    assert!(errors.is_empty(), "{}", errors.join("\n"));
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(8 * 1024 * 1024))
}

fn checked(engine: &Engine, source: &str) -> Engine {
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap()
        .engine
}

fn install(mut engine: Engine, names: &[&str]) -> Engine {
    let families: Vec<_> = engine
        .environment()
        .constants()
        .filter_map(|(_, info)| {
            if let ConstantInfo::Induct(ind) = info {
                Some(ind.clone())
            } else {
                None
            }
        })
        .collect();
    let recursors: Vec<_> = names
        .iter()
        .map(|n| {
            let Some(ConstantInfo::Rec(rec)) =
                engine.environment().find(&name(&format!("{n}.rec")))
            else {
                panic!("source recursor missing")
            };
            rec.clone()
        })
        .collect();
    let mut declarations = Vec::new();
    for rec in &recursors {
        declarations.push(below_declaration(rec, &families, generation_budget()).unwrap());
    }
    for rec in &recursors {
        declarations.extend(brec_on_declarations(rec, &families, generation_budget()).unwrap());
    }
    for definition in declarations {
        if let Some(ConstantInfo::Defn(existing)) = engine.environment().find(&definition.base.name)
        {
            assert_eq!(existing, &definition);
            continue;
        }
        engine = engine
            .admit_declaration(Declaration::Defn(definition), &KVMap::new(), limits())
            .unwrap()
            .into_complete()
            .expect("both seats check the candidate")
            .engine;
    }
    engine
}

#[test]
fn generated_course_of_values_proves_a_recursive_user_function() {
    let mut seed = Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap();
    // The source seed's PProd primitive omits its named projections. Real
    // Prelude already has these; admit the retained projection through both
    // seats to make the explicit recursive-history observation available.
    let ConstantInfo::Defn(projection) = &retained_prelude()[&name("PProd.fst")] else {
        panic!("retained PProd projection is a definition")
    };
    seed = seed
        .admit_declaration(
            Declaration::Defn(projection.clone()),
            &KVMap::new(),
            limits(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let base = checked(
        &seed,
        "inductive Chain where | nil | cons (head : Nat) (tail : Chain)",
    );
    let root = base.logical_root(&KVMap::new());
    let engine = install(base.clone(), &["Chain"]);
    assert_eq!(base.logical_root(&KVMap::new()), root);
    let source = "def sumStep (c : Chain) : @Chain.below (fun _ => Nat) c -> Nat :=\n\
        Chain.casesOn (motive := fun c => @Chain.below (fun _ => Nat) c -> Nat) c\n\
        (fun _ => 0) (fun head tail history => head + history.1)\n\
        theorem total_ok : @Chain.brecOn (fun _ => Nat)\n\
        (Chain.cons 20 (Chain.cons 22 Chain.nil)) sumStep = 42 := rfl";
    let result = checked(&engine, source);
    assert!(result.environment().contains(&name("total_ok")));
    assert!(
        engine.check_source_files(
            &[b"theorem wrong : @Chain.brecOn (fun _ => Nat) Chain.nil (fun _ _ => 1) = 2 := rfl"],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_err()
    );
}

#[test]
fn indexed_mutual_and_function_valued_histories_admit() {
    let seed = Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap();
    let engine = checked(
        &seed,
        "inductive Vec (A : Type) : Nat -> Type where\n\
         | nil : Vec A 0\n\
         | cons (n : Nat) (head : A) (tail : Vec A n) : Vec A (Nat.succ n)\n\
         inductive Branch where | leaf (n : Nat) | node (next : Nat -> Branch)\n\
         mutual\ninductive Tree where | node (forest : Forest)\n\
         inductive Forest where | nil | cons (tree : Tree) (rest : Forest)\nend",
    );
    let engine = install(engine, &["Vec", "Branch", "Tree", "Forest"]);
    checked(
        &engine,
        "theorem vec_base : @Vec.brecOn Nat (fun _ _ => Nat) 0 (@Vec.nil Nat) (fun _ _ _ => 42) = 42 := rfl\n\
         theorem branch_base : @Branch.brecOn (fun _ => Nat) (Branch.node (fun _ => Branch.leaf 3)) (fun _ _ => 42) = 42 := rfl\n\
         theorem tree_base : @Tree.brecOn (fun _ => Nat) (fun _ => Nat) (Tree.node Forest.nil) (fun _ _ => 42) (fun _ _ => 0) = 42 := rfl",
    );
}

#[test]
fn malformed_inputs_and_exhaustion_never_return_candidates() {
    let constants = retained_prelude();
    let rec = recursor(constants, "Nat.rec");
    let families = families(constants);
    assert_eq!(
        below_declaration(rec, &[], generation_budget()),
        Err(AuxiliaryError::InconsistentFamily)
    );
    let mut wrong = rec.clone();
    wrong.num_indices += 1;
    assert_eq!(
        below_declaration(&wrong, &families, generation_budget()),
        Err(AuxiliaryError::InvalidTelescope)
    );
    for budget in [
        RecordBudget {
            max_binders: 0,
            max_nodes: 10_000,
        },
        RecordBudget {
            max_binders: 1000,
            max_nodes: 0,
        },
    ] {
        assert_eq!(
            below_declaration(rec, &families, budget),
            Err(AuxiliaryError::ResourceLimit)
        );
        assert_eq!(
            brec_on_declarations(rec, &families, budget),
            Err(AuxiliaryError::ResourceLimit)
        );
    }
    assert!(
        below_declaration(
            recursor(constants, "And.rec"),
            &families,
            generation_budget()
        )
        .is_err()
    );
}

fn collect_paths(root: &Path, paths: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(root)
        .unwrap()
        .map(Result::unwrap)
        .collect();
    entries.sort_by_key(|entry| entry.file_name());
    for entry in entries {
        let kind = entry.file_type().unwrap();
        if kind.is_dir() {
            collect_paths(&entry.path(), paths);
        } else if kind.is_file() && entry.path().extension().is_some_and(|ext| ext == "olean") {
            paths.push(entry.path());
        }
    }
}

#[test]
fn pinned_stdlib_course_of_values_identity_frontier() {
    let Some(root) = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the required Reference corpus is absent"
        );
        eprintln!(
            "SKIP: full course-of-values frontier requires FLN_REFERENCE_LIB; retained Prelude still runs"
        );
        return;
    };
    let mut paths = Vec::new();
    collect_paths(&root, &mut paths);
    assert!(
        paths.len() >= 2000,
        "a fixture subset cannot satisfy the corpus gate"
    );
    let mut all_families = BTreeMap::new();
    let mut candidates = Vec::new();
    for path in &paths {
        let exported = std::fs::read(path).unwrap();
        let constants = if path.with_extension("olean.private").is_file() {
            decode_chain_constants_from_parts(
                &exported,
                &std::fs::read(path.with_extension("olean.server")).unwrap(),
                &std::fs::read(path.with_extension("olean.private")).unwrap(),
                ChainLimits::default(),
            )
            .unwrap()
            .constants
        } else {
            let view = OleanView::parse(&exported).unwrap();
            DeclDecoder::new(&view, WalkBudget::default())
                .decode_module_constants()
                .unwrap()
        };
        let constants: BTreeMap<_, _> = constants
            .into_iter()
            .map(|info| (info.name().clone(), info))
            .collect();
        for family in families(&constants) {
            all_families.insert(family.base.name.clone(), family);
        }
        candidates.extend(inventory(&constants));
    }
    let families: Vec<_> = all_families.into_values().collect();
    let errors = compare_candidates(&candidates, &families);
    let nested = candidates.iter().filter(|c| matches!(c.recursor.base.name.leaf_view(), LeafView::Str(s) if s.starts_with("rec_"))).count();
    eprintln!(
        "pinned stdlib course-of-values: modules={}, families={}, nested={}, definitions={}, mismatches={}",
        paths.len(),
        candidates.len(),
        nested,
        candidates.len() * 3,
        errors.len()
    );
    assert!(
        candidates.len() >= 100,
        "the generated population must cover real stdlib recursion"
    );
    assert!(
        errors.is_empty(),
        "{}",
        errors
            .iter()
            .take(20)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}
