//! Native `ctorIdx` / `toCtorIdx` candidate verification and whole-stdlib
//! derived-declaration suffix census (fln-derived-declaration-frontier-cj7s).
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, ExprNode};
use fln_core::name::{LeafView, Name};
use fln_elab::inductive::auxiliaries::{AuxiliaryError, CtorIdxConstMeta, ctor_idx_declarations};
use fln_elab::records::RecordBudget;
use fln_env::constants::{ConstantInfo, ConstructorVal, DefinitionVal, InductiveVal};
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

/// Structural equality modulo binder names (preserving binder infos, domains,
/// bodies, levels, literals, projections, and metadata), because `mkArrow`
/// attaches a per-module macro-hygiene suffix to the final non-dependent arrow
/// binder of `<T>.ctorIdx`'s type.
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

fn compare_ctor_idx(actual: &DefinitionVal, expected: &DefinitionVal) -> Result<(), String> {
    let type_ok = expr_eq_mod_binder_names(&actual.base.type_, &expected.base.type_);
    let value_ok = actual.value == expected.value;
    let levels_ok = actual.base.level_params == expected.base.level_params;
    let name_ok = actual.base.name == expected.base.name;
    let hints_ok = actual.hints == expected.hints;
    let safety_ok = actual.safety == expected.safety;
    let all_ok = actual.all == expected.all;
    if type_ok && value_ok && levels_ok && name_ok && hints_ok && safety_ok && all_ok {
        return Ok(());
    }
    Err(format!(
        "{}: type_mod_names={type_ok}, value_exact={value_ok}, levels={levels_ok}, name={name_ok}, hints={hints_ok} (actual={:?} expected={:?}), safety={safety_ok}, all={all_ok}",
        expected.base.name.to_display_string(),
        actual.hints,
        expected.hints,
    ))
}

fn collect_constructors(
    constants: &BTreeMap<Name, ConstantInfo>,
    inductive: &InductiveVal,
) -> Result<Vec<ConstructorVal>, String> {
    inductive
        .ctors
        .iter()
        .map(|ctor_name| match constants.get(ctor_name) {
            Some(ConstantInfo::Ctor(c)) => Ok(c.clone()),
            other => Err(format!(
                "{}: missing constructor {} (got {other:?})",
                inductive.base.name.to_display_string(),
                ctor_name.to_display_string()
            )),
        })
        .collect()
}

/// Known direct inductive auxiliary suffixes (never drops unknown suffixes:
/// any unrecognized suffix is returned as `None` and recorded under `unclassified`).
fn classify_inductive_suffix(suffix: &str) -> Option<&'static str> {
    match suffix {
        "rec" => Some("rec"),
        "recOn" => Some("recOn"),
        "casesOn" => Some("casesOn"),
        "below" => Some("below"),
        "ibelow" => Some("ibelow"),
        "brecOn" => Some("brecOn"),
        "binductionOn" => Some("binductionOn"),
        "ctorIdx" => Some("ctorIdx"),
        "toCtorIdx" => Some("toCtorIdx"),
        "ctorElim" => Some("ctorElim"),
        "ctorElimType" => Some("ctorElimType"),
        "noConfusion" => Some("noConfusion"),
        "noConfusionType" => Some("noConfusionType"),
        "sizeOf_spec" | "_sizeOf_inst" => Some("sizeOf"),
        _ if suffix.starts_with("rec_") && suffix[4..].chars().all(|c| c.is_ascii_digit()) => {
            Some("rec_nested")
        }
        _ if suffix.starts_with("below_") && suffix[6..].chars().all(|c| c.is_ascii_digit()) => {
            Some("below_nested")
        }
        _ if suffix.starts_with("brecOn_") && suffix[7..].chars().all(|c| c.is_ascii_digit()) => {
            Some("brecOn_nested")
        }
        _ if suffix.starts_with("_sizeOf_") => Some("sizeOf"),
        _ => None,
    }
}

fn compare_ctor_idx_population(
    constants: &BTreeMap<Name, ConstantInfo>,
    ambient: &BTreeMap<Name, CtorIdxConstMeta>,
) -> (usize, usize, Vec<String>) {
    let mut ctor_idx_count = 0;
    let mut to_ctor_idx_count = 0;
    let mut mismatches = Vec::new();
    for info in constants.values() {
        let ConstantInfo::Defn(expected) = info else {
            continue;
        };
        let LeafView::Str(suffix @ ("ctorIdx" | "toCtorIdx")) = expected.base.name.leaf_view()
        else {
            continue;
        };
        let family_name = expected.base.name.parent();
        let Some(ConstantInfo::Induct(inductive)) = constants.get(&family_name) else {
            continue;
        };
        let Some(ConstantInfo::Defn(cases_on)) =
            constants.get(&Name::str(family_name.clone(), "casesOn"))
        else {
            mismatches.push(format!(
                "{}: missing casesOn definition",
                expected.base.name.to_display_string()
            ));
            continue;
        };
        let ctors = match collect_constructors(constants, inductive) {
            Ok(ctors) => ctors,
            Err(err) => {
                mismatches.push(err);
                continue;
            }
        };
        let generated =
            ctor_idx_declarations(inductive, &ctors, cases_on, generation_budget(), |nm| {
                ambient
                    .get(nm)
                    .copied()
                    .or_else(|| constants.get(nm).map(CtorIdxConstMeta::from_constant))
            });
        match generated {
            Ok(Some(candidates)) => {
                if suffix == "ctorIdx" {
                    ctor_idx_count += 1;
                    if let Err(err) = compare_ctor_idx(&candidates.ctor_idx, expected) {
                        mismatches.push(err);
                    }
                } else {
                    to_ctor_idx_count += 1;
                    match candidates.to_ctor_idx {
                        Some(alias) => {
                            if let Err(err) = compare_ctor_idx(&alias, expected) {
                                mismatches.push(err);
                            }
                        }
                        None => mismatches.push(format!(
                            "{}: pin declared toCtorIdx but generator did not classify as enum",
                            expected.base.name.to_display_string()
                        )),
                    }
                }
            }
            Ok(None) => mismatches.push(format!(
                "{}: generator skipped auxiliary that pin declared",
                expected.base.name.to_display_string()
            )),
            Err(err) => {
                mismatches.push(format!("{}: {err}", expected.base.name.to_display_string()))
            }
        }
    }
    (ctor_idx_count, to_ctor_idx_count, mismatches)
}

#[test]
fn retained_prelude_ctor_idx_and_to_ctor_idx_match_pin_exactly() {
    let constants = retained_prelude();
    let ambient: BTreeMap<_, _> = constants
        .iter()
        .map(|(k, v)| (k.clone(), CtorIdxConstMeta::from_constant(v)))
        .collect();
    for expected_present in [
        "Nat.ctorIdx",
        "Bool.ctorIdx",
        "Bool.toCtorIdx",
        "List.ctorIdx",
    ] {
        assert!(
            matches!(
                constants.get(&name(expected_present)),
                Some(ConstantInfo::Defn(_))
            ),
            "retained Prelude must contain {expected_present}"
        );
    }
    let (ctor_idx_count, to_ctor_idx_count, mismatches) =
        compare_ctor_idx_population(constants, &ambient);
    eprintln!(
        "retained Prelude: ctorIdx={ctor_idx_count}, toCtorIdx={to_ctor_idx_count}, mismatches={}",
        mismatches.len()
    );
    assert!(
        ctor_idx_count >= 5 && to_ctor_idx_count >= 1,
        "anti-vacuity: retained Prelude must carry real ctorIdx/toCtorIdx definitions"
    );
    assert!(mismatches.is_empty(), "{}", mismatches.join("\n"));

    // Prop-former families (Eq, False, And) must be skipped by the guard.
    for prop_family in ["Eq", "False", "And"] {
        let Some(ConstantInfo::Induct(ind)) = constants.get(&name(prop_family)) else {
            panic!("missing {prop_family}");
        };
        let Some(ConstantInfo::Defn(cases_on)) =
            constants.get(&Name::str(name(prop_family), "casesOn"))
        else {
            panic!("missing {prop_family}.casesOn");
        };
        let ctors = collect_constructors(constants, ind).unwrap();
        assert_eq!(
            ctor_idx_declarations(ind, &ctors, cases_on, generation_budget(), |nm| {
                ambient.get(nm).copied()
            }),
            Ok(None),
            "Prop-former {prop_family} must not generate ctorIdx"
        );
    }
}

#[test]
fn ctor_idx_mutants_and_error_guards_are_killed() {
    let constants = retained_prelude();
    let ambient: BTreeMap<_, _> = constants
        .iter()
        .map(|(k, v)| (k.clone(), CtorIdxConstMeta::from_constant(v)))
        .collect();
    let Some(ConstantInfo::Induct(nat_ind)) = constants.get(&name("Nat")) else {
        panic!("missing Nat");
    };
    let Some(ConstantInfo::Defn(nat_cases)) = constants.get(&name("Nat.casesOn")) else {
        panic!("missing Nat.casesOn");
    };
    let Some(ConstantInfo::Defn(nat_expected)) = constants.get(&name("Nat.ctorIdx")) else {
        panic!("missing Nat.ctorIdx");
    };
    let nat_ctors = collect_constructors(constants, nat_ind).unwrap();

    // Mutant 1: swapped constructor cidx must fail exact value comparison.
    let mut swapped_ctors = nat_ctors.clone();
    swapped_ctors[0].cidx = 1;
    swapped_ctors[1].cidx = 0;
    let mutated = ctor_idx_declarations(
        nat_ind,
        &swapped_ctors,
        nat_cases,
        generation_budget(),
        |nm| ambient.get(nm).copied(),
    )
    .unwrap()
    .unwrap();
    assert!(
        compare_ctor_idx(&mutated.ctor_idx, nat_expected).is_err(),
        "mutant swapping constructor indices must fail comparison"
    );

    // Mutant 2: wrong binder info on a parameter in List.ctorIdx type must fail comparison.
    let Some(ConstantInfo::Defn(list_expected)) = constants.get(&name("List.ctorIdx")) else {
        panic!("missing List.ctorIdx");
    };
    let mut wrong_bi = list_expected.clone();
    if let ExprNode::ForallE {
        binder_name,
        binder_type,
        body,
        ..
    } = list_expected.base.type_.node()
    {
        wrong_bi.base.type_ = Expr::forall_e(
            binder_name.clone(),
            binder_type.clone(),
            body.clone(),
            BinderInfo::Default,
        );
    }
    assert!(
        compare_ctor_idx(&wrong_bi, list_expected).is_err(),
        "mutant changing implicit parameter binder info must fail comparison"
    );

    // Mutant 3: classifier must never drop an unknown suffix.
    assert_eq!(classify_inductive_suffix("unheardOfAuxiliary"), None);
    assert_eq!(classify_inductive_suffix("ctorIdx"), Some("ctorIdx"));

    // Error & budget guards.
    assert_eq!(
        ctor_idx_declarations(nat_ind, &[], nat_cases, generation_budget(), |_| None),
        Err(AuxiliaryError::InconsistentFamily)
    );
    let mut wrong_cases = nat_cases.clone();
    wrong_cases.base.name = name("Nat.notCasesOn");
    assert_eq!(
        ctor_idx_declarations(
            nat_ind,
            &nat_ctors,
            &wrong_cases,
            generation_budget(),
            |_| None
        ),
        Err(AuxiliaryError::InconsistentFamily)
    );
    assert_eq!(
        ctor_idx_declarations(
            nat_ind,
            &nat_ctors,
            nat_cases,
            RecordBudget {
                max_binders: 0,
                max_nodes: 1000,
            },
            |_| None
        ),
        Err(AuxiliaryError::ResourceLimit)
    );
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

fn decode_module(path: &Path) -> Vec<ConstantInfo> {
    let exported = std::fs::read(path).unwrap();
    if path.with_extension("olean.private").is_file() {
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
    }
}

#[test]
fn pinned_stdlib_ctor_idx_and_suffix_census_frontier() {
    let Some(root) = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "FLN_REQUIRE_REFERENCE needs FLN_REFERENCE_LIB for the whole-stdlib ctorIdx frontier"
        );
        eprintln!(
            "SKIP: pinned stdlib ctorIdx frontier requires FLN_REFERENCE_LIB; retained Prelude comparisons still run"
        );
        return;
    };
    let mut files = Vec::new();
    collect_olean_paths(&root, &mut files);
    assert!(
        files.len() >= 2000,
        "anti-vacuity: whole-stdlib scan requires >= 2000 .olean modules, found {}",
        files.len()
    );

    // Pass 1: collect ambient regular heights & unsafe flags across all stdlib modules
    // (mirrors the cumulative environment getMaxHeight sees when elaborating a module),
    // plus record all inductive names and direct child suffixes for the cj7s census.
    let mut per_module: Vec<(PathBuf, BTreeMap<Name, ConstantInfo>)> =
        Vec::with_capacity(files.len());
    let mut ambient: BTreeMap<Name, CtorIdxConstMeta> = BTreeMap::new();
    let mut inductive_count = 0_usize;
    let mut classified_suffixes: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut unclassified_suffixes: BTreeMap<String, usize> = BTreeMap::new();

    for path in files {
        let constants: BTreeMap<Name, ConstantInfo> = decode_module(&path)
            .into_iter()
            .map(|info| {
                ambient.insert(info.name().clone(), CtorIdxConstMeta::from_constant(&info));
                (info.name().clone(), info)
            })
            .collect();
        for info in constants.values() {
            if matches!(info, ConstantInfo::Induct(_)) {
                inductive_count += 1;
            }
        }
        // Suffix census: every constant whose direct parent is an inductive declared in the
        // same module (excluding the inductive's own constructors).
        let mut ctor_names: BTreeSet<Name> = BTreeSet::new();
        for info in constants.values() {
            if let ConstantInfo::Induct(ind) = info {
                ctor_names.extend(ind.ctors.iter().cloned());
            }
        }
        for const_name in constants.keys() {
            if ctor_names.contains(const_name) {
                continue;
            }
            let parent = const_name.parent();
            if !matches!(constants.get(&parent), Some(ConstantInfo::Induct(_))) {
                continue;
            }
            if let LeafView::Str(suffix) = const_name.leaf_view() {
                if let Some(kind) = classify_inductive_suffix(suffix) {
                    *classified_suffixes.entry(kind).or_default() += 1;
                } else {
                    *unclassified_suffixes.entry(suffix.to_owned()).or_default() += 1;
                }
            }
        }
        per_module.push((path, constants));
    }

    let mut ctor_idx_total = 0_usize;
    let mut to_ctor_idx_total = 0_usize;
    let mut mismatches = Vec::new();
    for (path, constants) in &per_module {
        let (ci, tci, errs) = compare_ctor_idx_population(constants, &ambient);
        ctor_idx_total += ci;
        to_ctor_idx_total += tci;
        mismatches.extend(errs.into_iter().map(|e| format!("{}: {e}", path.display())));
    }

    eprintln!(
        "pinned stdlib derived census: modules={}, inductives={}, ctorIdx={ctor_idx_total}, toCtorIdx={to_ctor_idx_total}, mismatches={}",
        per_module.len(),
        inductive_count,
        mismatches.len()
    );
    eprintln!("classified suffix histogram: {classified_suffixes:?}");
    eprintln!(
        "unclassified suffix count={} (top 20: {:?})",
        unclassified_suffixes.len(),
        {
            let mut pairs: Vec<_> = unclassified_suffixes.iter().collect();
            pairs.sort_by(|a, b| b.1.cmp(a.1).then_with(|| a.0.cmp(b.0)));
            pairs.into_iter().take(20).collect::<Vec<_>>()
        }
    );
    assert!(
        inductive_count >= 500 && ctor_idx_total >= 500,
        "anti-vacuity: stdlib must contain >= 500 inductives and ctorIdx definitions"
    );
    assert!(
        mismatches.is_empty(),
        "first mismatches:\n{}",
        mismatches
            .iter()
            .take(20)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}
