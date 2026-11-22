//! Native `ctorElimType`, `ctorElim`, and `<ctor>.elim` verification against
//! the retained pinned Lean 4 v4.32.0 Prelude and optional whole-stdlib sweep
//! (fln-derived-declaration-frontier-cj7s).
#![forbid(unsafe_code)]

use fln_core::expr::{Expr, ExprNode};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_elab::inductive::auxiliaries::{AuxiliaryError, ctor_elim_declarations};
use fln_elab::records::RecordBudget;
use fln_env::constants::{ConstantInfo, ConstructorVal, DefinitionVal};
use fln_olean::decl::{ChainLimits, DeclDecoder, decode_chain_constants_from_parts};
use fln_olean::region::{OleanView, WalkBudget};
use std::collections::{BTreeMap, BTreeSet};
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

/// Structural equality modulo binder names (`mkArrow` inside `mkIndCtorElim`
/// attaches a per-module macro-hygiene suffix to its non-dependent arrow binder).
fn expr_eq_mod_binder_names(left: &Expr, right: &Expr) -> bool {
    let mut stack = vec![(left, right)];
    let mut seen = BTreeSet::new();
    while let Some((a, b)) = stack.pop() {
        if a == b {
            continue;
        }
        let pair = (a.allocation_identity(), b.allocation_identity());
        if !seen.insert(pair) {
            continue;
        }
        match (a.node(), b.node()) {
            (ExprNode::App { f: af, a: aa }, ExprNode::App { f: bf, a: ba }) => {
                stack.push((aa, ba));
                stack.push((af, bf));
            }
            (
                ExprNode::Lam {
                    binder_type: at,
                    body: ab,
                    binder_info: ai,
                    ..
                },
                ExprNode::Lam {
                    binder_type: bt,
                    body: bb,
                    binder_info: bi,
                    ..
                },
            )
            | (
                ExprNode::ForallE {
                    binder_type: at,
                    body: ab,
                    binder_info: ai,
                    ..
                },
                ExprNode::ForallE {
                    binder_type: bt,
                    body: bb,
                    binder_info: bi,
                    ..
                },
            ) => {
                if ai != bi {
                    return false;
                }
                stack.push((ab, bb));
                stack.push((at, bt));
            }
            (
                ExprNode::LetE {
                    type_: at,
                    value: av,
                    body: ab,
                    non_dep: an,
                    ..
                },
                ExprNode::LetE {
                    type_: bt,
                    value: bv,
                    body: bb,
                    non_dep: bn,
                    ..
                },
            ) => {
                if an != bn {
                    return false;
                }
                stack.push((ab, bb));
                stack.push((av, bv));
                stack.push((at, bt));
            }
            (
                ExprNode::Proj {
                    struct_name: at,
                    idx: ai,
                    expr: ae,
                },
                ExprNode::Proj {
                    struct_name: bt,
                    idx: bi,
                    expr: be,
                },
            ) => {
                if at != bt || ai != bi {
                    return false;
                }
                stack.push((ae, be));
            }
            (ExprNode::MData { data: ad, expr: ae }, ExprNode::MData { data: bd, expr: be }) => {
                if ad != bd {
                    return false;
                }
                stack.push((ae, be));
            }
            _ => return false,
        }
    }
    true
}

fn compare_def(actual: &DefinitionVal, expected: &DefinitionVal) -> Result<(), String> {
    let type_ok = expr_eq_mod_binder_names(&actual.base.type_, &expected.base.type_);
    let value_ok = expr_eq_mod_binder_names(&actual.value, &expected.value);
    let levels_ok = actual.base.level_params == expected.base.level_params;
    let name_ok = actual.base.name == expected.base.name;
    let hints_ok = actual.hints == expected.hints;
    let safety_ok = actual.safety == expected.safety;
    let all_ok = actual.all == expected.all;
    if type_ok && value_ok && levels_ok && name_ok && hints_ok && safety_ok && all_ok {
        return Ok(());
    }
    Err(format!(
        "{}: name_ok={name_ok} levels_ok={levels_ok} hints_ok={hints_ok} ({:?} vs {:?}) \
         safety_ok={safety_ok} ({:?} vs {:?}) all_ok={all_ok} type_ok={type_ok} value_ok={value_ok}",
        expected.base.name.to_display_string(),
        actual.hints,
        expected.hints,
        actual.safety,
        expected.safety,
    ))
}

#[derive(Default)]
struct CtorElimStats {
    elim_type_population: usize,
    elim_type_identical: usize,
    elim_population: usize,
    elim_identical: usize,
    ctor_elim_population: usize,
    ctor_elim_identical: usize,
    mismatches: Vec<String>,
}

fn verify_ctor_elim_population(constants: &BTreeMap<Name, ConstantInfo>) -> CtorElimStats {
    let mut stats = CtorElimStats::default();
    let budget = generation_budget();

    for (ind_name, info) in constants {
        let ConstantInfo::Induct(inductive) = info else {
            continue;
        };
        let cet_name = Name::str(ind_name.clone(), "ctorElimType");
        let ce_name = Name::str(ind_name.clone(), "ctorElim");
        let expected_cet = match constants.get(&cet_name) {
            Some(ConstantInfo::Defn(def)) => Some(def),
            _ => None,
        };
        let expected_ce = match constants.get(&ce_name) {
            Some(ConstantInfo::Defn(def)) => Some(def),
            _ => None,
        };
        if expected_cet.is_none() && expected_ce.is_none() {
            continue;
        }
        let cases_on_name = Name::str(ind_name.clone(), "casesOn");
        let Some(ConstantInfo::Defn(cases_on)) = constants.get(&cases_on_name) else {
            stats.mismatches.push(format!(
                "{}: has ctorElimType/ctorElim without casesOn",
                ind_name.to_display_string()
            ));
            continue;
        };
        let ctors: Vec<ConstructorVal> = inductive
            .ctors
            .iter()
            .filter_map(|cn| match constants.get(cn) {
                Some(ConstantInfo::Ctor(c)) => Some(c.clone()),
                _ => None,
            })
            .collect();
        let generated =
            match ctor_elim_declarations(inductive, &ctors, cases_on, budget, |n| constants.get(n))
            {
                Ok(Some(c)) => c,
                Ok(None) => {
                    stats.mismatches.push(format!(
                        "{}: generator skipped inductive that has pin ctorElim",
                        ind_name.to_display_string()
                    ));
                    continue;
                }
                Err(err) => {
                    stats.mismatches.push(format!(
                        "{}: generator errored: {err}",
                        ind_name.to_display_string()
                    ));
                    continue;
                }
            };

        if let Some(exp) = expected_cet {
            stats.elim_type_population += 1;
            match compare_def(&generated.ctor_elim_type, exp) {
                Ok(()) => stats.elim_type_identical += 1,
                Err(msg) => stats.mismatches.push(msg),
            }
        }
        if let Some(exp) = expected_ce {
            stats.elim_population += 1;
            match compare_def(&generated.ctor_elim, exp) {
                Ok(()) => stats.elim_identical += 1,
                Err(msg) => stats.mismatches.push(msg),
            }
        }
        for actual_c in &generated.constructor_elims {
            if let Some(ConstantInfo::Defn(exp_c)) = constants.get(&actual_c.base.name) {
                stats.ctor_elim_population += 1;
                match compare_def(actual_c, exp_c) {
                    Ok(()) => stats.ctor_elim_identical += 1,
                    Err(msg) => stats.mismatches.push(msg),
                }
            }
        }
    }
    stats
}

#[test]
fn retained_prelude_ctor_elim_family_is_identical() {
    let prelude = retained_prelude();
    let stats = verify_ctor_elim_population(prelude);
    eprintln!(
        "retained Prelude ctorElim: ctorElimType={}/{}, ctorElim={}/{}, ctor.elim={}/{}, mismatches={}",
        stats.elim_type_identical,
        stats.elim_type_population,
        stats.elim_identical,
        stats.elim_population,
        stats.ctor_elim_identical,
        stats.ctor_elim_population,
        stats.mismatches.len(),
    );
    assert!(
        stats.mismatches.is_empty(),
        "Prelude ctorElim mismatches ({}):\n{}",
        stats.mismatches.len(),
        stats
            .mismatches
            .iter()
            .take(10)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
    assert!(
        stats.elim_type_population >= 12,
        "anti-vacuity: expected >= 12 Prelude ctorElimType defs, got {}",
        stats.elim_type_population
    );
    assert!(
        stats.elim_population >= 12,
        "anti-vacuity: expected >= 12 Prelude ctorElim defs, got {}",
        stats.elim_population
    );
    assert!(
        stats.ctor_elim_population >= 39,
        "anti-vacuity: expected >= 39 Prelude <ctor>.elim defs, got {}",
        stats.ctor_elim_population
    );
    assert_eq!(stats.elim_type_identical, stats.elim_type_population);
    assert_eq!(stats.elim_identical, stats.elim_population);
    assert_eq!(stats.ctor_elim_identical, stats.ctor_elim_population);
}

#[test]
fn ctor_elim_mutants_and_guards_are_killed() {
    let prelude = retained_prelude();
    let ConstantInfo::Induct(nat_ind) = prelude.get(&name("Nat")).unwrap() else {
        panic!("Nat inductive missing");
    };
    let ConstantInfo::Defn(nat_cases) = prelude.get(&name("Nat.casesOn")).unwrap() else {
        panic!("Nat.casesOn missing");
    };
    let ConstantInfo::Defn(nat_cet) = prelude.get(&name("Nat.ctorElimType")).unwrap() else {
        panic!("Nat.ctorElimType missing");
    };
    let ConstantInfo::Defn(nat_ce) = prelude.get(&name("Nat.ctorElim")).unwrap() else {
        panic!("Nat.ctorElim missing");
    };
    let nat_ctors: Vec<ConstructorVal> = nat_ind
        .ctors
        .iter()
        .map(|cn| match prelude.get(cn).unwrap() {
            ConstantInfo::Ctor(c) => c.clone(),
            _ => panic!("expected ctor"),
        })
        .collect();

    let generated =
        ctor_elim_declarations(nat_ind, &nat_ctors, nat_cases, generation_budget(), |n| {
            prelude.get(n)
        })
        .expect("Nat ctorElim succeeds")
        .expect("Nat has ctorElim");
    assert!(compare_def(&generated.ctor_elim_type, nat_cet).is_ok());
    assert!(compare_def(&generated.ctor_elim, nat_ce).is_ok());

    // Mutant 1: wrong level param in ctorElimType must fail comparison.
    let mut bad_cet = generated.ctor_elim_type.clone();
    bad_cet.base.level_params = vec![Name::from_components(["wrong"])];
    assert!(compare_def(&bad_cet, nat_cet).is_err());

    // Mutant 2: wrong universe on ctorElim value must fail comparison.
    let mut bad_ce = generated.ctor_elim.clone();
    bad_ce.value = Expr::sort(Level::zero());
    assert!(compare_def(&bad_ce, nat_ce).is_err());

    // Guard 1: single-constructor type (Prod) returns Ok(None).
    let ConstantInfo::Induct(prod_ind) = prelude.get(&name("Prod")).unwrap() else {
        panic!("Prod missing");
    };
    let ConstantInfo::Defn(prod_cases) = prelude.get(&name("Prod.casesOn")).unwrap() else {
        panic!("Prod.casesOn missing");
    };
    let prod_ctors: Vec<ConstructorVal> = prod_ind
        .ctors
        .iter()
        .map(|cn| match prelude.get(cn).unwrap() {
            ConstantInfo::Ctor(c) => c.clone(),
            _ => panic!("expected ctor"),
        })
        .collect();
    assert_eq!(
        ctor_elim_declarations(
            prod_ind,
            &prod_ctors,
            prod_cases,
            generation_budget(),
            |n| prelude.get(n)
        )
        .expect("Prod guard succeeds"),
        None
    );

    // Guard 2: tiny budget returns ResourceLimit (never panics).
    let tiny = RecordBudget {
        max_binders: 4096,
        max_nodes: 4,
    };
    assert_eq!(
        ctor_elim_declarations(nat_ind, &nat_ctors, nat_cases, tiny, |n| prelude.get(n)),
        Err(AuxiliaryError::ResourceLimit)
    );
}

fn collect_olean_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    let mut paths: Vec<PathBuf> = entries.flatten().map(|e| e.path()).collect();
    paths.sort();
    for path in paths {
        if path.is_dir() {
            collect_olean_files(&path, out);
        } else if path.extension().and_then(|s| s.to_str()) == Some("olean") {
            out.push(path);
        }
    }
}

fn load_module_constants(olean_path: &Path, out: &mut BTreeMap<Name, ConstantInfo>) {
    let server = olean_path.with_extension("olean.server");
    let private = olean_path.with_extension("olean.private");
    let Ok(base_bytes) = std::fs::read(olean_path) else {
        return;
    };
    if server.is_file() && private.is_file() {
        let Ok(srv_bytes) = std::fs::read(&server) else {
            return;
        };
        let Ok(priv_bytes) = std::fs::read(&private) else {
            return;
        };
        if let Ok(decoded) = decode_chain_constants_from_parts(
            &base_bytes,
            &srv_bytes,
            &priv_bytes,
            ChainLimits::default(),
        ) {
            for info in decoded.constants {
                out.insert(info.name().clone(), info);
            }
        }
        return;
    }
    if let Ok(view) = OleanView::parse(&base_bytes)
        && let Ok(constants) =
            DeclDecoder::new(&view, WalkBudget::default()).decode_module_constants()
    {
        for info in constants {
            out.insert(info.name().clone(), info);
        }
    }
}

/// Pin-gated whole-stdlib `ctorElimType` / `ctorElim` / `<ctor>.elim` scan.
#[test]
fn reference_stdlib_ctor_elim_frontier() {
    let Ok(ref_lib) = std::env::var("FLN_REFERENCE_LIB") else {
        eprintln!(
            "SKIP: set FLN_REFERENCE_LIB to pinned lean lib/lean to run whole-stdlib ctorElim scan"
        );
        return;
    };
    let lib_root = PathBuf::from(&ref_lib);
    assert!(
        lib_root.is_dir(),
        "FLN_REFERENCE_LIB is not a directory: {ref_lib}"
    );
    let mut olean_files = Vec::new();
    collect_olean_files(&lib_root, &mut olean_files);
    assert!(
        olean_files.len() >= 1000,
        "anti-vacuity: expected >= 1000 stdlib .olean files, got {}",
        olean_files.len()
    );
    let mut constants = BTreeMap::new();
    for path in &olean_files {
        load_module_constants(path, &mut constants);
    }
    let stats = verify_ctor_elim_population(&constants);
    eprintln!(
        "WHOLE-STDLIB ctorElim ({} modules, {} constants): ctorElimType={}/{}, ctorElim={}/{}, ctor.elim={}/{}, mismatches={}",
        olean_files.len(),
        constants.len(),
        stats.elim_type_identical,
        stats.elim_type_population,
        stats.elim_identical,
        stats.elim_population,
        stats.ctor_elim_identical,
        stats.ctor_elim_population,
        stats.mismatches.len(),
    );
    assert!(
        stats.mismatches.is_empty(),
        "whole-stdlib ctorElim mismatches ({}):\n{}",
        stats.mismatches.len(),
        stats
            .mismatches
            .iter()
            .take(20)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}
