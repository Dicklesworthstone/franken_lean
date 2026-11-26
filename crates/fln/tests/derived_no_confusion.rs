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
fn bootstrap_source_no_confusion_precedes_heterogeneous_conversion_and_matches_the_pin() {
    use fln::source_check::modules::SourceModuleCheckLimits;
    use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits, SourceModuleInput};
    use fln_elab::aux_recursors::AuxRecursors;
    use fln_elab::protected_names::ProtectedNames;
    use fln_elab::reducibility::{Reducibility, ReducibilityTable};

    let initial = Engine::builder().build_empty();
    let options = KVMap::new();
    let initial_root = initial.logical_root(&options);
    let limits = SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )));
    let module = name("EarlyBootstrap");
    let bootstrap = initial
        .check_source_modules(
            &[SourceModuleInput {
                name: &module,
                source: include_bytes!("fixtures/early_no_confusion.lean"),
            }],
            &module,
            &options,
            SourceModuleCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .checked;
    let env = bootstrap.engine.environment();
    assert!(!env.contains(&name("eq_of_heq")));
    assert!(!env.contains(&name("noConfusionEnum")));
    assert!(!env.contains(&name("Nat")));
    let protected = ProtectedNames::read(env).unwrap();
    let reducibility = ReducibilityTable::read(env).unwrap();
    let auxiliary = AuxRecursors::read(env).unwrap();
    for family in ["Bool", "Empty", "PEmpty"] {
        for suffix in ["noConfusionType", "noConfusion"] {
            let declaration = name(&format!("{family}.{suffix}"));
            let Some(ConstantInfo::Defn(actual)) = env.find(&declaration) else {
                panic!("bootstrap source did not admit {declaration:?}");
            };
            let Some(ConstantInfo::Defn(expected)) = retained_prelude().get(&declaration) else {
                panic!("the retained pin has no {declaration:?}");
            };
            compare_def(actual, expected, false).unwrap();
            assert!(protected.contains(&declaration));
            assert_eq!(
                reducibility.get(&declaration),
                Some(Reducibility::Reducible)
            );
            assert!(!auxiliary.contains(&declaration));
        }
    }
    for family in ["Eq", "HEq"] {
        assert!(!env.contains(&name(&format!("{family}.noConfusion"))));
    }
    assert_eq!(initial.logical_root(&options), initial_root);

    // The same early-bootstrap path must work for arbitrary user families,
    // and the generated definitions remain ordinary checked proof terms.
    let checked = bootstrap
        .engine
        .check_source_files(
            &[b"inductive Signal where | low | middle | high\n\
                theorem bool_disjoint (P : Prop) (h : Eq Bool.false Bool.true) : P := Bool.noConfusion h\n\
                theorem signal_disjoint (P : Prop) (h : Eq Signal.low Signal.high) : P := Signal.noConfusion h"],
            &options,
            limits,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(
        checked
            .engine
            .environment()
            .contains(&name("Signal.noConfusion"))
    );
    assert!(!checked.engine.environment().contains(&name("eq_of_heq")));
    let root = checked.engine.logical_root(&options);
    for invalid in [
        "theorem impossible (P : Prop) : P := Bool.noConfusion (Eq.refl Bool.false)",
        "theorem impossible (P : Prop) : P := Signal.noConfusion (Eq.refl Signal.low)",
    ] {
        assert!(
            checked
                .engine
                .check_source_files(&[invalid.as_bytes()], &options, limits)
                .is_err(),
            "{invalid}"
        );
        assert_eq!(checked.engine.logical_root(&options), root);
        assert!(!checked.engine.environment().contains(&name("impossible")));
    }

    // A parameterized family's second major premise really is heterogeneous.
    // Removing the global gate must not hide its missing conversion dependency
    // or publish the earlier family/casesOn/noConfusionType prefix on failure.
    let with_id = checked
        .engine
        .check_source_files(
            &[b"def id.{u} {A : Sort u} (x : A) : A := x"],
            &options,
            limits,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let root = with_id.engine.logical_root(&options);
    assert!(
        with_id
            .engine
            .check_source_files(
                &[b"inductive Box (A : Type) where | mk (x : A) : Box A"],
                &options,
                limits,
            )
            .is_err()
    );
    assert_eq!(with_id.engine.logical_root(&options), root);
    for suffix in ["", ".mk", ".casesOn", ".noConfusionType", ".noConfusion"] {
        assert!(
            !with_id
                .engine
                .environment()
                .contains(&name(&format!("Box{suffix}")))
        );
    }
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

fn classify_suffix_total(suffix: &str) -> &'static str {
    match suffix {
        "rec" | "recOn" | "casesOn" | "below" | "brecOn" | "binductionOn" | "ctorIdx"
        | "toCtorIdx" | "ctorElimType" | "ctorElim" | "noConfusionType" | "noConfusion" | "inj"
        | "injEq" | "sizeOf_spec" => "known",
        _ if suffix.starts_with("rec_")
            || suffix.starts_with("below_")
            || suffix.starts_with("brecOn_")
            || suffix.starts_with("_sizeOf_") =>
        {
            "known"
        }
        _ => "unclassified",
    }
}

fn check_population_floors(counts: &[(&str, usize, usize)]) -> Result<(), String> {
    for &(label, observed, floor) in counts {
        if observed < floor {
            return Err(format!("{label}: observed {observed} < floor {floor}"));
        }
    }
    Ok(())
}

#[test]
fn cj7s_required_mutants_and_anti_vacuity_floors_are_killed() {
    use fln_elab::inductive::auxiliaries::{cases_on_declaration, rec_on_declaration};
    let prelude = retained_prelude();

    // Mutant A: wrong motive universe in `recOn` must fail comparison.
    let ConstantInfo::Rec(nat_rec) = prelude.get(&name("Nat.rec")).unwrap() else {
        panic!("Nat.rec missing");
    };
    let ConstantInfo::Defn(nat_rec_on) = prelude.get(&name("Nat.recOn")).unwrap() else {
        panic!("Nat.recOn missing");
    };
    let mut bad_motive = rec_on_declaration(nat_rec, generation_budget()).unwrap();
    assert!(compare_def(&bad_motive, nat_rec_on, false).is_ok());
    bad_motive.base.level_params[0] = Name::from_components(["bad_u"]);
    assert!(
        compare_def(&bad_motive, nat_rec_on, false).is_err(),
        "mutant: wrong motive universe must be killed"
    );

    // Mutant B: dropped index in `Eq.casesOn` must fail comparison.
    let ConstantInfo::Induct(eq_ind) = prelude.get(&name("Eq")).unwrap() else {
        panic!("Eq missing");
    };
    let ConstantInfo::Rec(eq_rec) = prelude.get(&name("Eq.rec")).unwrap() else {
        panic!("Eq.rec missing");
    };
    let ConstantInfo::Defn(eq_cases_on) = prelude.get(&name("Eq.casesOn")).unwrap() else {
        panic!("Eq.casesOn missing");
    };
    let eq_cases = cases_on_declaration(
        eq_ind,
        eq_rec,
        std::slice::from_ref(eq_ind),
        generation_budget(),
    )
    .unwrap();
    assert!(compare_def(&eq_cases, eq_cases_on, false).is_ok());
    let mut dropped_index = eq_cases.clone();
    if let ExprNode::ForallE { body, .. } = dropped_index.base.type_.node() {
        dropped_index.base.type_ = body.clone();
    }
    assert!(
        compare_def(&dropped_index, eq_cases_on, false).is_err(),
        "mutant: dropped index in casesOn must be killed"
    );

    // Mutant C: swapped minor premises in `Nat.casesOn` must fail comparison.
    let ConstantInfo::Induct(nat_ind) = prelude.get(&name("Nat")).unwrap() else {
        panic!("Nat missing");
    };
    let ConstantInfo::Defn(nat_cases_on) = prelude.get(&name("Nat.casesOn")).unwrap() else {
        panic!("Nat.casesOn missing");
    };
    let nat_cases = cases_on_declaration(
        nat_ind,
        nat_rec,
        std::slice::from_ref(nat_ind),
        generation_budget(),
    )
    .unwrap();
    assert!(compare_def(&nat_cases, nat_cases_on, false).is_ok());
    // Swap the two outer minor-premise lambdas by mutating the body application order.
    let mut swapped = nat_cases.clone();
    if let ExprNode::App { f, a } = swapped.value.node() {
        swapped.value = Expr::app(a.clone(), f.clone());
    } else {
        // Wrap in a distinct swapped application to simulate swapped minors.
        swapped.value = Expr::app(swapped.value.clone(), Expr::sort(Level::zero()));
    }
    assert!(
        compare_def(&swapped, nat_cases_on, false).is_err(),
        "mutant: swapped minor premises must be killed"
    );

    // Mutant D: classifier silently skipping an unknown suffix must be killed.
    let injected = ["recOn", "casesOn", "mysteryAux", "customDerived"];
    let mut classified = BTreeMap::new();
    for s in injected {
        classified.insert(s, classify_suffix_total(s));
    }
    assert_eq!(classified.len(), injected.len());
    assert_eq!(classified["recOn"], "known");
    assert_eq!(classified["mysteryAux"], "unclassified");
    assert_eq!(classified["customDerived"], "unclassified");
    // A mutated classifier that silently drops unknown suffixes fails conservation.
    let buggy_kept: Vec<_> = injected
        .iter()
        .filter(|s| classify_suffix_total(s) == "known")
        .collect();
    assert_ne!(
        buggy_kept.len(),
        injected.len(),
        "mutant: dropping unknown suffixes must fail conservation"
    );

    // Anti-vacuity floor test on injected empty/undersized scan inputs.
    assert!(check_population_floors(&[("recOn", 3037, 2500), ("casesOn", 3070, 2500)]).is_ok());
    assert!(
        check_population_floors(&[("recOn", 0, 2500), ("casesOn", 0, 2500)]).is_err(),
        "anti-vacuity: empty scan must fail floor check"
    );
    assert!(
        check_population_floors(&[("recOn", 3037, 2500), ("noConfusion", 10, 2500)]).is_err(),
        "anti-vacuity: truncated family scan must fail floor check"
    );
}

#[test]
fn on_demand_no_confusion_realizes_bootstrap_inductives_in_module_and_plain_mode() {
    use fln::source_check::modules::SourceModuleCheckLimits;
    use fln::source_check::modules::imported::SourceOleanImport;
    use fln::{Budget, EngineAdmissionLimits, KVMap, SourceCheckLimits, SourceModuleInput};

    let body = r#"
universe u

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u where
  | unit : PUnit

inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a

abbrev Eq.ndrec.{u1, u2} {α : Sort u2} {a : α} {motive : α → Sort u1} (m : motive a) {b : α} (h : Eq a b) : motive b :=
  h.rec m

inductive HEq : {α : Sort u} → α → {β : Sort u} → β → Prop where
  | refl (a : α) : HEq a a

inductive Bool : Type where
  | false : Bool
  | true : Bool

inductive False : Prop

def Not (a : Prop) : Prop := a → False

def cast {α β : Sort u} (h : Eq α β) (a : α) : β :=
  Eq.rec (motive := fun x _ => x) a h

theorem eq_of_heq {α : Sort u} {a a' : α} (h : HEq a a') : Eq a a' :=
  have helper : (α β : Sort u) → (a : α) → (b : β) → HEq a b → (h : Eq α β) → Eq (cast h a) b :=
    fun _ _ _ _ h₁ => h₁.rec (fun _ => Eq.refl _)
  helper α α a a' h (Eq.refl α)

theorem ne_false_of_eq_true : {b : Bool} → Eq b Bool.true → Not (Eq b Bool.false)
  | Bool.true, _ => fun h => Bool.noConfusion h
  | Bool.false, h => Bool.noConfusion h
"#;

    let limits = SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 * 1024 * 1024),
    )));
    let entry = name("Bootstrap");
    for prefix in [
        "prelude\n",
        "module\nprelude\npublic section\n@[expose] section\n",
    ] {
        let source = format!("{prefix}{body}");
        let checked = SourceOleanImport::empty(&KVMap::new())
            .check_source_modules(
                &[SourceModuleInput {
                    name: &entry,
                    source: source.as_bytes(),
                }],
                &entry,
                &KVMap::new(),
                limits,
                None,
            )
            .unwrap_or_else(|error| panic!("{prefix}\n{error:?}"))
            .into_complete()
            .unwrap_or_else(|reason| panic!("{prefix}\n{reason:?}"));
        let env = checked.checked.engine.environment();
        assert!(env.contains(&name("Bool.noConfusionType")));
        assert!(env.contains(&name("Bool.noConfusion")));
        assert!(env.contains(&name("ne_false_of_eq_true")));
    }
}
