//! Whole-stdlib derived-declaration frontier probe (`fln-derived-declaration-frontier-cj7s`).
//!
//! Decodes every `.olean` (with `.olean.server`/`.olean.private` when present) under a
//! pinned Reference `lib/lean` root, builds the complete suffix histogram over all
//! inductive families (reporting any unclassified suffix rather than silently skipping it),
//! and regenerates `recOn`, `casesOn`, `ctorIdx`, `toCtorIdx`, `ctorElimType`, `ctorElim`,
//! and `<ctor>.elim` via `fln-elab`'s native generators, comparing each against the decoded
//! pin declaration.
#![forbid(unsafe_code)]

use fln_core::expr::{Expr, ExprNode};
use fln_core::name::{LeafView, Name};
use fln_elab::inductive::auxiliaries::{
    CtorIdxConstMeta, cases_on_declaration, ctor_elim_declarations, ctor_idx_declarations,
    rec_on_declaration,
};
use fln_elab::records::RecordBudget;
use fln_env::constants::{ConstantInfo, ConstructorVal, DefinitionVal, InductiveVal};
use fln_olean::decl::{ChainLimits, DeclDecoder, decode_chain_constants_from_parts};
use fln_olean::region::{OleanView, WalkBudget};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Instant;

fn generation_budget() -> RecordBudget {
    RecordBudget {
        max_binders: 4096,
        max_nodes: 20_000_000,
    }
}

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

#[derive(Default)]
struct FamilyTally {
    population: usize,
    identical: usize,
    statement_identical: usize,
    mismatches: usize,
    first_mismatch: Option<String>,
}

impl FamilyTally {
    fn record_def(&mut self, actual: &DefinitionVal, expected: &DefinitionVal) {
        self.population += 1;
        let name_ok = actual.base.name == expected.base.name;
        let levels_ok = actual.base.level_params == expected.base.level_params;
        let type_ok = expr_eq_mod_binder_names(&actual.base.type_, &expected.base.type_);
        let value_ok = expr_eq_mod_binder_names(&actual.value, &expected.value);
        let hints_ok = actual.hints == expected.hints;
        let safety_ok = actual.safety == expected.safety;
        let all_ok = actual.all == expected.all;
        if name_ok && levels_ok && type_ok && value_ok && hints_ok && safety_ok && all_ok {
            self.identical += 1;
        } else if name_ok && levels_ok && type_ok {
            self.statement_identical += 1;
            self.mismatches += 1;
            if self.first_mismatch.is_none() {
                self.first_mismatch = Some(format!(
                    "{}: statement-identical (value_ok={value_ok} hints={:?} vs {:?} safety={:?} vs {:?} all_ok={all_ok})",
                    expected.base.name.to_display_string(),
                    actual.hints,
                    expected.hints,
                    actual.safety,
                    expected.safety,
                ));
            }
        } else {
            self.mismatches += 1;
            if self.first_mismatch.is_none() {
                self.first_mismatch = Some(format!(
                    "{}: mismatch (name_ok={name_ok} levels_ok={levels_ok} type_ok={type_ok} value_ok={value_ok} hints={:?} vs {:?} safety={:?} vs {:?})",
                    expected.base.name.to_display_string(),
                    actual.hints,
                    expected.hints,
                    actual.safety,
                    expected.safety,
                ));
            }
        }
    }

    fn record_error(&mut self, label: &Name, detail: String) {
        self.population += 1;
        self.mismatches += 1;
        if self.first_mismatch.is_none() {
            self.first_mismatch = Some(format!("{}: {detail}", label.to_display_string()));
        }
    }

    fn print(&self, label: &str) {
        println!(
            "  {label:<16} identical={:>5}/{:<5}  stmt_only={:>4}  mismatches={:>4}{}",
            self.identical,
            self.population,
            self.statement_identical,
            self.mismatches,
            match &self.first_mismatch {
                Some(first) => format!("  first={first}"),
                None => String::new(),
            }
        );
    }
}

fn classify_derived_suffix(suffix: &str) -> Option<&'static str> {
    match suffix {
        "rec" | "recOn" | "casesOn" | "below" | "brecOn" | "binductionOn" | "ctorIdx"
        | "toCtorIdx" | "ctorElimType" | "ctorElim" | "noConfusionType" | "noConfusion" | "inj"
        | "injEq" | "sizeOf_spec" => Some("known"),
        _ if suffix.starts_with("rec_")
            || suffix.starts_with("below_")
            || suffix.starts_with("brecOn_")
            || suffix.starts_with("_sizeOf_") =>
        {
            Some("known")
        }
        _ => None,
    }
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

fn load_module_constants(
    olean_path: &Path,
    exported_out: &mut BTreeMap<Name, ConstantInfo>,
    full_out: &mut BTreeMap<Name, ConstantInfo>,
) {
    let server = olean_path.with_extension("olean.server");
    let private = olean_path.with_extension("olean.private");
    let Ok(base_bytes) = std::fs::read(olean_path) else {
        return;
    };
    if let Ok(view) = OleanView::parse(&base_bytes)
        && let Ok(constants) =
            DeclDecoder::new(&view, WalkBudget::default()).decode_module_constants()
    {
        for info in constants {
            exported_out.insert(info.name().clone(), info);
        }
    }
    if server.is_file()
        && private.is_file()
        && let (Ok(srv_bytes), Ok(priv_bytes)) = (std::fs::read(&server), std::fs::read(&private))
        && let Ok(decoded) = decode_chain_constants_from_parts(
            &base_bytes,
            &srv_bytes,
            &priv_bytes,
            ChainLimits::default(),
        )
    {
        for info in decoded.constants {
            full_out.insert(info.name().clone(), info);
        }
        return;
    }
    if let Ok(view) = OleanView::parse(&base_bytes)
        && let Ok(constants) =
            DeclDecoder::new(&view, WalkBudget::default()).decode_module_constants()
    {
        for info in constants {
            full_out.insert(info.name().clone(), info);
        }
    }
}

fn is_private_name(name: &Name) -> bool {
    let mut cur = name.clone();
    while !cur.is_anonymous() {
        if cur.parent().is_anonymous() {
            return matches!(cur.leaf_view(), LeafView::Str("_private"));
        }
        cur = cur.parent();
    }
    false
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let report_only = args.iter().any(|a| a == "--report-only");
    let lib_dir = args
        .iter()
        .find(|a| !a.starts_with('-'))
        .cloned()
        .or_else(|| std::env::var("FLN_REFERENCE_LIB").ok())
        .unwrap_or_else(|| {
            "/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean".to_owned()
        });
    let lib_path = PathBuf::from(&lib_dir);
    if !lib_path.is_dir() {
        eprintln!("derived-frontier-probe: not a directory: {lib_dir}");
        return ExitCode::from(2);
    }

    let start = Instant::now();
    let mut olean_files = Vec::new();
    collect_olean_files(&lib_path, &mut olean_files);
    let mut exported_constants = BTreeMap::new();
    let mut constants = BTreeMap::new();
    for path in &olean_files {
        load_module_constants(path, &mut exported_constants, &mut constants);
    }
    let decode_elapsed = start.elapsed();

    let mut ind_names = BTreeSet::new();
    let mut single_inds = 0usize;
    let mut mutual_inds = 0usize;
    let mut nested_inds = 0usize;
    for (name, info) in &constants {
        if let ConstantInfo::Induct(ind) = info {
            ind_names.insert(name.clone());
            if ind.num_nested > 0 {
                nested_inds += 1;
            } else if ind.all.len() > 1 {
                mutual_inds += 1;
            } else {
                single_inds += 1;
            }
        }
    }

    // Derived suffix histogram over immediate children of inductive names.
    let mut known_suffixes: BTreeMap<String, usize> = BTreeMap::new();
    let mut other_suffixes: BTreeMap<String, usize> = BTreeMap::new();
    for (name, info) in &constants {
        if matches!(info, ConstantInfo::Ctor(_)) {
            continue;
        }
        let parent = name.parent();
        if ind_names.contains(&parent)
            && let LeafView::Str(leaf) = name.leaf_view()
        {
            if classify_derived_suffix(leaf).is_some() {
                *known_suffixes.entry(leaf.to_owned()).or_default() += 1;
            } else {
                *other_suffixes.entry(leaf.to_owned()).or_default() += 1;
            }
        }
    }

    let budget = generation_budget();
    let mut rec_on_tally = FamilyTally::default();
    let mut cases_on_tally = FamilyTally::default();
    let mut ctor_idx_tally = FamilyTally::default();
    let mut to_ctor_idx_tally = FamilyTally::default();
    let mut ctor_elim_type_tally = FamilyTally::default();
    let mut ctor_elim_tally = FamilyTally::default();
    let mut constructor_elim_tally = FamilyTally::default();

    for ind_name in &ind_names {
        let Some(ConstantInfo::Induct(inductive)) = constants.get(ind_name) else {
            continue;
        };
        let block: Vec<InductiveVal> = inductive
            .all
            .iter()
            .filter_map(|m| match constants.get(m) {
                Some(ConstantInfo::Induct(iv)) => Some(iv.clone()),
                _ => None,
            })
            .collect();
        let ctors: Vec<ConstructorVal> = inductive
            .ctors
            .iter()
            .filter_map(|cn| match constants.get(cn) {
                Some(ConstantInfo::Ctor(c)) => Some(c.clone()),
                _ => None,
            })
            .collect();

        // recOn & casesOn
        let rec_name = Name::str(ind_name.clone(), "rec");
        if let Some(ConstantInfo::Rec(recursor)) = constants.get(&rec_name) {
            let rec_on_name = Name::str(ind_name.clone(), "recOn");
            if let Some(ConstantInfo::Defn(exp)) = constants.get(&rec_on_name) {
                match rec_on_declaration(recursor, budget) {
                    Ok(act) => rec_on_tally.record_def(&act, exp),
                    Err(e) => rec_on_tally.record_error(&rec_on_name, e.to_string()),
                }
            }
            let cases_on_name = Name::str(ind_name.clone(), "casesOn");
            if let Some(ConstantInfo::Defn(exp)) = constants.get(&cases_on_name) {
                match cases_on_declaration(inductive, recursor, &block, budget) {
                    Ok(act) => cases_on_tally.record_def(&act, exp),
                    Err(e) => cases_on_tally.record_error(&cases_on_name, e.to_string()),
                }
            }
        }

        // ctorIdx / toCtorIdx
        let cases_on_name = Name::str(ind_name.clone(), "casesOn");
        let cases_on_opt = match constants.get(&cases_on_name) {
            Some(ConstantInfo::Defn(def)) => Some(def),
            _ => None,
        };
        let ctor_idx_name = Name::str(ind_name.clone(), "ctorIdx");
        let to_ctor_idx_name = Name::str(ind_name.clone(), "toCtorIdx");
        let exp_ci = match constants.get(&ctor_idx_name) {
            Some(ConstantInfo::Defn(def)) => Some(def),
            _ => None,
        };
        let exp_tci = match constants.get(&to_ctor_idx_name) {
            Some(ConstantInfo::Defn(def)) => Some(def),
            _ => None,
        };
        if (exp_ci.is_some() || exp_tci.is_some())
            && let Some(cases_on) = cases_on_opt
        {
            // Match `CtorIdx.lean:43`: `withExporting (isExporting := !isPrivateName indName)`
            // so public inductives compute `getMaxHeight` against exported `.olean` declarations.
            let exporting = !is_private_name(ind_name);
            match ctor_idx_declarations(inductive, &ctors, cases_on, budget, |n| {
                let info = if exporting {
                    exported_constants.get(n).or_else(|| constants.get(n))
                } else {
                    constants.get(n)
                };
                info.map(CtorIdxConstMeta::from_constant)
            }) {
                Ok(Some(cands)) => {
                    if let Some(exp) = exp_ci {
                        ctor_idx_tally.record_def(&cands.ctor_idx, exp);
                    }
                    if let Some(exp) = exp_tci {
                        match &cands.to_ctor_idx {
                            Some(act) => to_ctor_idx_tally.record_def(act, exp),
                            None => to_ctor_idx_tally.record_error(
                                &to_ctor_idx_name,
                                "generator returned None for pin toCtorIdx".to_owned(),
                            ),
                        }
                    }
                }
                Ok(None) => {
                    if exp_ci.is_some() {
                        ctor_idx_tally.record_error(
                            &ctor_idx_name,
                            "generator returned None for pin ctorIdx".to_owned(),
                        );
                    }
                }
                Err(e) => {
                    if exp_ci.is_some() {
                        ctor_idx_tally.record_error(&ctor_idx_name, e.to_string());
                    }
                }
            }
        }

        // ctorElimType / ctorElim / <ctor>.elim
        let cet_name = Name::str(ind_name.clone(), "ctorElimType");
        let ce_name = Name::str(ind_name.clone(), "ctorElim");
        let exp_cet = match constants.get(&cet_name) {
            Some(ConstantInfo::Defn(def)) => Some(def),
            _ => None,
        };
        let exp_ce = match constants.get(&ce_name) {
            Some(ConstantInfo::Defn(def)) => Some(def),
            _ => None,
        };
        if (exp_cet.is_some() || exp_ce.is_some())
            && let Some(cases_on) = cases_on_opt
        {
            match ctor_elim_declarations(inductive, &ctors, cases_on, budget, |n| constants.get(n))
            {
                Ok(Some(cands)) => {
                    if let Some(exp) = exp_cet {
                        ctor_elim_type_tally.record_def(&cands.ctor_elim_type, exp);
                    }
                    if let Some(exp) = exp_ce {
                        ctor_elim_tally.record_def(&cands.ctor_elim, exp);
                    }
                    for act_c in &cands.constructor_elims {
                        if let Some(ConstantInfo::Defn(exp_c)) = constants.get(&act_c.base.name) {
                            constructor_elim_tally.record_def(act_c, exp_c);
                        }
                    }
                }
                Ok(None) => {
                    if exp_cet.is_some() {
                        ctor_elim_type_tally.record_error(
                            &cet_name,
                            "generator returned None for pin ctorElimType".to_owned(),
                        );
                    }
                }
                Err(e) => {
                    if exp_cet.is_some() {
                        ctor_elim_type_tally.record_error(&cet_name, e.to_string());
                    }
                }
            }
        }
    }

    let total_elapsed = start.elapsed();
    println!(
        "DERIVED FRONTIER PROBE: modules={} constants={} inductives={} (single={} mutual={} nested={}) decode={:.2}s total={:.2}s",
        olean_files.len(),
        constants.len(),
        ind_names.len(),
        single_inds,
        mutual_inds,
        nested_inds,
        decode_elapsed.as_secs_f64(),
        total_elapsed.as_secs_f64(),
    );
    println!("=== GENERATOR PARITY ===");
    rec_on_tally.print("recOn");
    cases_on_tally.print("casesOn");
    ctor_idx_tally.print("ctorIdx");
    to_ctor_idx_tally.print("toCtorIdx");
    ctor_elim_type_tally.print("ctorElimType");
    ctor_elim_tally.print("ctorElim");
    constructor_elim_tally.print("ctor.elim");

    println!("=== KNOWN DERIVED SUFFIX HISTOGRAM ===");
    let mut known_sorted: Vec<_> = known_suffixes.into_iter().collect();
    known_sorted.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    for (suffix, count) in known_sorted {
        println!("  {count:>5}  .{suffix}");
    }
    println!(
        "=== TOP 25 OTHER IMMEDIATE-CHILD SUFFIXES (projections / user defs / unclassified) ==="
    );
    let mut other_sorted: Vec<_> = other_suffixes.into_iter().collect();
    other_sorted.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    for (suffix, count) in other_sorted.into_iter().take(25) {
        println!("  {count:>5}  .{suffix}");
    }

    let total_mismatches = rec_on_tally.mismatches
        + cases_on_tally.mismatches
        + ctor_idx_tally.mismatches
        + to_ctor_idx_tally.mismatches
        + ctor_elim_type_tally.mismatches
        + ctor_elim_tally.mismatches
        + constructor_elim_tally.mismatches;
    if total_mismatches == 0 || report_only {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    }
}
