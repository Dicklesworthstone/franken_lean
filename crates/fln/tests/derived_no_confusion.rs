//! Native `noConfusionType` and `noConfusion` verification against the retained
//! pinned Lean 4 v4.32.0 Prelude and optional whole-stdlib sweep
//! (fln-derived-declaration-frontier-cj7s).
#![forbid(unsafe_code)]

use fln_core::expr::{Expr, ExprNode};
use fln_core::level::{Level, LevelView};
use fln_core::name::Name;
use fln_elab::inductive::auxiliaries::{AuxiliaryError, no_confusion_declarations};
use fln_elab::records::RecordBudget;
use fln_env::constants::{ConstantInfo, ConstructorVal, DefinitionVal};
use fln_olean::decl::{ChainLimits, decode_chain_constants_from_parts};
use std::collections::{BTreeMap, BTreeSet};
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

fn level_eq_mod_param_map(left: &Level, right: &Level, map: &BTreeMap<Name, Name>) -> bool {
    if map.is_empty() && left == right {
        return true;
    }
    match (left.view(), right.view()) {
        (LevelView::Zero, LevelView::Zero) => true,
        (LevelView::Succ(a), LevelView::Succ(b)) => level_eq_mod_param_map(a, b, map),
        (LevelView::Max(a1, a2), LevelView::Max(b1, b2))
        | (LevelView::IMax(a1, a2), LevelView::IMax(b1, b2)) => {
            level_eq_mod_param_map(a1, b1, map) && level_eq_mod_param_map(a2, b2, map)
        }
        (LevelView::Param(a), LevelView::Param(b)) => map.get(a).unwrap_or(a) == b,
        (LevelView::MVar(a), LevelView::MVar(b)) => a == b,
        _ => false,
    }
}

fn expr_eq_mod_binder_and_level_names(
    left: &Expr,
    right: &Expr,
    level_map: &BTreeMap<Name, Name>,
) -> bool {
    let mut stack = vec![(left, right)];
    let mut seen = BTreeSet::new();
    while let Some((a, b)) = stack.pop() {
        if level_map.is_empty() && a == b {
            continue;
        }
        if !seen.insert((a.allocation_identity(), b.allocation_identity())) {
            continue;
        }
        match (a.node(), b.node()) {
            (ExprNode::Sort { level: la }, ExprNode::Sort { level: lb }) => {
                if !level_eq_mod_param_map(la, lb, level_map) {
                    return false;
                }
            }
            (
                ExprNode::Const {
                    name: na,
                    levels: la,
                },
                ExprNode::Const {
                    name: nb,
                    levels: lb,
                },
            ) => {
                if na != nb
                    || la.len() != lb.len()
                    || !la
                        .iter()
                        .zip(lb)
                        .all(|(x, y)| level_eq_mod_param_map(x, y, level_map))
                {
                    return false;
                }
            }
            (ExprNode::BVar { idx: x }, ExprNode::BVar { idx: y }) => {
                if x != y {
                    return false;
                }
            }
            (ExprNode::FVar { id: x }, ExprNode::FVar { id: y }) => {
                if x != y {
                    return false;
                }
            }
            (ExprNode::MVar { id: x }, ExprNode::MVar { id: y }) => {
                if x != y {
                    return false;
                }
            }
            (ExprNode::Lit { literal: x }, ExprNode::Lit { literal: y }) => {
                if x != y {
                    return false;
                }
            }
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

fn compare_def(
    actual: &DefinitionVal,
    expected: &DefinitionVal,
    alpha_first_level: bool,
) -> Result<(), String> {
    let name_ok = actual.base.name == expected.base.name;
    let mut level_map = BTreeMap::new();
    let levels_ok = if alpha_first_level
        && actual.base.level_params.len() == expected.base.level_params.len()
        && !actual.base.level_params.is_empty()
    {
        if actual.base.level_params[0] != expected.base.level_params[0] {
            level_map.insert(
                actual.base.level_params[0].clone(),
                expected.base.level_params[0].clone(),
            );
        }
        actual.base.level_params[1..] == expected.base.level_params[1..]
    } else {
        actual.base.level_params == expected.base.level_params
    };
    let type_ok =
        expr_eq_mod_binder_and_level_names(&actual.base.type_, &expected.base.type_, &level_map);
    let value_ok = expr_eq_mod_binder_and_level_names(&actual.value, &expected.value, &level_map);
    let hints_ok = actual.hints == expected.hints;
    let safety_ok = actual.safety == expected.safety;
    let all_ok = actual.all == expected.all;
    if name_ok && levels_ok && type_ok && value_ok && hints_ok && safety_ok && all_ok {
        return Ok(());
    }
    Err(format!(
        "{}: name_ok={name_ok} levels_ok={levels_ok} type_ok={type_ok} value_ok={value_ok} \
         hints={:?} vs {:?} safety={:?} vs {:?} all_ok={all_ok}",
        expected.base.name.to_display_string(),
        actual.hints,
        expected.hints,
        actual.safety,
        expected.safety,
    ))
}

#[test]
fn retained_prelude_no_confusion_family_is_identical() {
    let prelude = retained_prelude();
    let budget = generation_budget();
    let mut nct_pop = 0usize;
    let mut nct_ok = 0usize;
    let mut nc_pop = 0usize;
    let mut nc_ok = 0usize;
    let mut mismatches = Vec::new();

    // `noConfusionEnum` is defined in `Init.Core`, so every Prelude inductive
    // uses `mkNoConfusionCore` (`use_enum_helper = false`).
    for (ind_name, info) in prelude {
        let ConstantInfo::Induct(inductive) = info else {
            continue;
        };
        let nct_name = Name::str(ind_name.clone(), "noConfusionType");
        let nc_name = Name::str(ind_name.clone(), "noConfusion");
        let exp_nct = match prelude.get(&nct_name) {
            Some(ConstantInfo::Defn(d)) => Some(d),
            _ => None,
        };
        let exp_nc = match prelude.get(&nc_name) {
            Some(ConstantInfo::Defn(d)) => Some(d),
            _ => None,
        };
        if exp_nct.is_none() && exp_nc.is_none() {
            continue;
        }
        let cases_on_name = Name::str(ind_name.clone(), "casesOn");
        let Some(ConstantInfo::Defn(cases_on)) = prelude.get(&cases_on_name) else {
            mismatches.push(format!("{}: missing casesOn", ind_name.to_display_string()));
            continue;
        };
        let ctors: Vec<ConstructorVal> = inductive
            .ctors
            .iter()
            .filter_map(|cn| match prelude.get(cn) {
                Some(ConstantInfo::Ctor(c)) => Some(c.clone()),
                _ => None,
            })
            .collect();
        let generated =
            match no_confusion_declarations(inductive, &ctors, cases_on, false, budget, |n| {
                prelude.get(n)
            }) {
                Ok(Some(c)) => c,
                Ok(None) => {
                    mismatches.push(format!(
                        "{}: generator returned None",
                        ind_name.to_display_string()
                    ));
                    continue;
                }
                Err(e) => {
                    mismatches.push(format!(
                        "{}: generator error: {e}",
                        ind_name.to_display_string()
                    ));
                    continue;
                }
            };
        if let Some(exp) = exp_nct {
            nct_pop += 1;
            match compare_def(
                &generated.no_confusion_type,
                exp,
                generated.is_enum_construction,
            ) {
                Ok(()) => nct_ok += 1,
                Err(msg) => mismatches.push(msg),
            }
        }
        if let Some(exp) = exp_nc {
            nc_pop += 1;
            match compare_def(&generated.no_confusion, exp, generated.is_enum_construction) {
                Ok(()) => nc_ok += 1,
                Err(msg) => mismatches.push(msg),
            }
        }
    }

    eprintln!(
        "retained Prelude noConfusion: noConfusionType={nct_ok}/{nct_pop}, noConfusion={nc_ok}/{nc_pop}, mismatches={}",
        mismatches.len()
    );
    assert!(
        mismatches.is_empty(),
        "Prelude noConfusion mismatches ({}):\n{}",
        mismatches.len(),
        mismatches
            .iter()
            .take(10)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
    // Anti-vacuity floor over retained Init/Prelude.olean (includes Nat, Bool,
    // Option, List, Prod, Subtype, Fin, ForIn', Trans, etc.).
    assert!(
        nct_pop >= 100,
        "anti-vacuity: expected >= 100 Prelude noConfusionType defs, got {nct_pop}"
    );
    assert!(
        nc_pop >= 100,
        "anti-vacuity: expected >= 100 Prelude noConfusion defs, got {nc_pop}"
    );
    assert_eq!(nct_ok, nct_pop);
    assert_eq!(nc_ok, nc_pop);
}

#[test]
fn no_confusion_mutants_and_guards_are_killed() {
    let prelude = retained_prelude();
    let ConstantInfo::Induct(nat_ind) = prelude.get(&name("Nat")).unwrap() else {
        panic!("Nat inductive missing");
    };
    let ConstantInfo::Defn(nat_cases) = prelude.get(&name("Nat.casesOn")).unwrap() else {
        panic!("Nat.casesOn missing");
    };
    let ConstantInfo::Defn(nat_nct) = prelude.get(&name("Nat.noConfusionType")).unwrap() else {
        panic!("Nat.noConfusionType missing");
    };
    let ConstantInfo::Defn(nat_nc) = prelude.get(&name("Nat.noConfusion")).unwrap() else {
        panic!("Nat.noConfusion missing");
    };
    let nat_ctors: Vec<ConstructorVal> = nat_ind
        .ctors
        .iter()
        .map(|cn| match prelude.get(cn).unwrap() {
            ConstantInfo::Ctor(c) => c.clone(),
            _ => panic!("expected ctor"),
        })
        .collect();

    let generated = no_confusion_declarations(
        nat_ind,
        &nat_ctors,
        nat_cases,
        false,
        generation_budget(),
        |n| prelude.get(n),
    )
    .expect("Nat noConfusion succeeds")
    .expect("Nat has noConfusion");
    assert!(compare_def(&generated.no_confusion_type, nat_nct, false).is_ok());
    assert!(compare_def(&generated.no_confusion, nat_nc, false).is_ok());

    // Mutant 1: wrong level parameter fails comparison.
    let mut bad_nct = generated.no_confusion_type.clone();
    bad_nct.base.level_params = vec![Name::from_components(["wrong"])];
    assert!(compare_def(&bad_nct, nat_nct, false).is_err());

    // Mutant 2: mutated value fails comparison.
    let mut bad_nc = generated.no_confusion.clone();
    bad_nc.value = Expr::sort(Level::zero());
    assert!(compare_def(&bad_nc, nat_nc, false).is_err());

    // Mutant 3: enabling `use_enum_helper = true` on `Bool` switches to the
    // `noConfusionEnum` fast path, which must NOT match Prelude's core `Bool.noConfusion`.
    let ConstantInfo::Induct(bool_ind) = prelude.get(&name("Bool")).unwrap() else {
        panic!("Bool missing");
    };
    let ConstantInfo::Defn(bool_cases) = prelude.get(&name("Bool.casesOn")).unwrap() else {
        panic!("Bool.casesOn missing");
    };
    let ConstantInfo::Defn(bool_nc) = prelude.get(&name("Bool.noConfusion")).unwrap() else {
        panic!("Bool.noConfusion missing");
    };
    let bool_ctors: Vec<ConstructorVal> = bool_ind
        .ctors
        .iter()
        .map(|cn| match prelude.get(cn).unwrap() {
            ConstantInfo::Ctor(c) => c.clone(),
            _ => panic!("expected ctor"),
        })
        .collect();
    let enum_gen = no_confusion_declarations(
        bool_ind,
        &bool_ctors,
        bool_cases,
        true,
        generation_budget(),
        |n| prelude.get(n),
    )
    .expect("Bool enum path succeeds")
    .expect("Bool enum path produces candidates");
    assert!(enum_gen.is_enum_construction);
    assert!(compare_def(&enum_gen.no_confusion, bool_nc, true).is_err());

    // Guard 1: Prop inductive (`Eq` / `True`) returns Ok(None).
    let ConstantInfo::Induct(eq_ind) = prelude.get(&name("Eq")).unwrap() else {
        panic!("Eq missing");
    };
    let ConstantInfo::Defn(eq_cases) = prelude.get(&name("Eq.casesOn")).unwrap() else {
        panic!("Eq.casesOn missing");
    };
    let eq_ctors: Vec<ConstructorVal> = eq_ind
        .ctors
        .iter()
        .map(|cn| match prelude.get(cn).unwrap() {
            ConstantInfo::Ctor(c) => c.clone(),
            _ => panic!("expected ctor"),
        })
        .collect();
    assert_eq!(
        no_confusion_declarations(
            eq_ind,
            &eq_ctors,
            eq_cases,
            false,
            generation_budget(),
            |n| prelude.get(n)
        )
        .expect("Eq guard succeeds"),
        None
    );

    // Guard 2: tiny budget fails closed with ResourceLimit (never panics).
    let tiny = RecordBudget {
        max_binders: 4096,
        max_nodes: 4,
    };
    assert_eq!(
        no_confusion_declarations(nat_ind, &nat_ctors, nat_cases, false, tiny, |n| {
            prelude.get(n)
        }),
        Err(AuxiliaryError::ResourceLimit)
    );
}
