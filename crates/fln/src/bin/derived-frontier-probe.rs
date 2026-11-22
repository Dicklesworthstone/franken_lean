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
use fln_core::level::{Level, LevelView};
use fln_core::name::{LeafView, Name};
use fln_elab::inductive::auxiliaries::{
    CtorIdxConstMeta, below_declaration, brec_on_declarations, cases_on_declaration,
    ctor_elim_declarations, ctor_idx_declarations, no_confusion_declarations, rec_on_declaration,
};
use fln_elab::records::RecordBudget;
use fln_env::constants::{ConstantInfo, ConstructorVal, DefinitionVal, InductiveVal, RecursorVal};
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

fn level_eq_mod_param_map(a: &Level, b: &Level, map: &BTreeMap<Name, Name>) -> bool {
    if map.is_empty() && a == b {
        return true;
    }
    match (a.view(), b.view()) {
        (LevelView::Zero, LevelView::Zero) => true,
        (LevelView::Succ(x), LevelView::Succ(y)) => level_eq_mod_param_map(x, y, map),
        (LevelView::Max(x1, x2), LevelView::Max(y1, y2))
        | (LevelView::IMax(x1, x2), LevelView::IMax(y1, y2)) => {
            level_eq_mod_param_map(x1, y1, map) && level_eq_mod_param_map(x2, y2, map)
        }
        (LevelView::Param(na), LevelView::Param(nb)) => map.get(na).unwrap_or(na) == nb,
        (LevelView::MVar(ma), LevelView::MVar(mb)) => ma == mb,
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
        let pair = (a.allocation_identity(), b.allocation_identity());
        if !seen.insert(pair) {
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

fn first_expr_diff(left: &Expr, right: &Expr, level_map: &BTreeMap<Name, Name>) -> Option<String> {
    let mut stack = vec![("root".to_owned(), left, right)];
    let mut seen = BTreeSet::new();
    while let Some((path, a, b)) = stack.pop() {
        if level_map.is_empty() && a == b {
            continue;
        }
        if !seen.insert((a.allocation_identity(), b.allocation_identity())) {
            continue;
        }
        match (a.node(), b.node()) {
            (ExprNode::Sort { level: la }, ExprNode::Sort { level: lb }) => {
                if !level_eq_mod_param_map(la, lb, level_map) {
                    return Some(format!("{path}: Sort({la:?}) != Sort({lb:?})"));
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
                    return Some(format!(
                        "{path}: Const({} {la:?}) != Const({} {lb:?})",
                        na.to_display_string(),
                        nb.to_display_string()
                    ));
                }
            }
            (ExprNode::BVar { idx: x }, ExprNode::BVar { idx: y }) => {
                if x != y {
                    return Some(format!("{path}: BVar({x}) != BVar({y})"));
                }
            }
            (ExprNode::FVar { id: x }, ExprNode::FVar { id: y }) => {
                if x != y {
                    return Some(format!("{path}: FVar({x:?}) != FVar({y:?})"));
                }
            }
            (ExprNode::MVar { id: x }, ExprNode::MVar { id: y }) => {
                if x != y {
                    return Some(format!("{path}: MVar({x:?}) != MVar({y:?})"));
                }
            }
            (ExprNode::Lit { literal: x }, ExprNode::Lit { literal: y }) => {
                if x != y {
                    return Some(format!("{path}: Lit({x:?}) != Lit({y:?})"));
                }
            }
            (ExprNode::App { f: af, a: aa }, ExprNode::App { f: bf, a: ba }) => {
                stack.push((format!("{path}.a"), aa, ba));
                stack.push((format!("{path}.f"), af, bf));
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
            ) => {
                if ai != bi {
                    return Some(format!("{path}: Lam binder_info {ai:?} != {bi:?}"));
                }
                stack.push((format!("{path}.lam_body"), ab, bb));
                stack.push((format!("{path}.lam_ty"), at, bt));
            }
            (
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
                    return Some(format!("{path}: ForallE binder_info {ai:?} != {bi:?}"));
                }
                stack.push((format!("{path}.pi_body"), ab, bb));
                stack.push((format!("{path}.pi_ty"), at, bt));
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
                    return Some(format!("{path}: LetE non_dep {an} != {bn}"));
                }
                stack.push((format!("{path}.let_body"), ab, bb));
                stack.push((format!("{path}.let_val"), av, bv));
                stack.push((format!("{path}.let_ty"), at, bt));
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
                    return Some(format!("{path}: Proj({at:?},{ai}) != Proj({bt:?},{bi})"));
                }
                stack.push((format!("{path}.proj"), ae, be));
            }
            (ExprNode::MData { data: ad, expr: ae }, ExprNode::MData { data: bd, expr: be }) => {
                if ad != bd {
                    return Some(format!("{path}: MData mismatch"));
                }
                stack.push((format!("{path}.mdata"), ae, be));
            }
            _ => {
                return Some(format!(
                    "{path}: node shape {:?} != {:?}",
                    std::mem::discriminant(a.node()),
                    std::mem::discriminant(b.node())
                ));
            }
        }
    }
    None
}

#[derive(Default)]
struct FamilyTally {
    population: usize,
    identical: usize,
    statement_identical: usize,
    mismatches: usize,
    first_mismatch: Option<String>,
    samples: Vec<String>,
}

impl FamilyTally {
    fn record_def_with_alpha_levels(
        &mut self,
        actual: &DefinitionVal,
        expected: &DefinitionVal,
        alpha_first_level: bool,
    ) {
        self.population += 1;
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
        let type_ok = expr_eq_mod_binder_and_level_names(
            &actual.base.type_,
            &expected.base.type_,
            &level_map,
        );
        let value_ok =
            expr_eq_mod_binder_and_level_names(&actual.value, &expected.value, &level_map);
        let hints_ok = actual.hints == expected.hints;
        let safety_ok = actual.safety == expected.safety;
        let all_ok = actual.all == expected.all;
        if name_ok && levels_ok && type_ok && value_ok && hints_ok && safety_ok && all_ok {
            self.identical += 1;
        } else if name_ok && levels_ok && type_ok {
            self.statement_identical += 1;
            self.mismatches += 1;
            let diff = first_expr_diff(&actual.value, &expected.value, &level_map)
                .unwrap_or_else(|| "meta-only".to_owned());
            let msg = format!(
                "{}: statement-identical (value_ok={value_ok} hints={:?} vs {:?} safety={:?} vs {:?} all_ok={all_ok} diff={diff})",
                expected.base.name.to_display_string(),
                actual.hints,
                expected.hints,
                actual.safety,
                expected.safety,
            );
            if self.first_mismatch.is_none() {
                self.first_mismatch = Some(msg.clone());
            }
            if self.samples.len() < 10 {
                self.samples.push(msg);
            }
        } else {
            self.mismatches += 1;
            let diff = if !type_ok {
                format!(
                    "type_diff={}",
                    first_expr_diff(&actual.base.type_, &expected.base.type_, &level_map)
                        .unwrap_or_default()
                )
            } else {
                format!(
                    "val_diff={}",
                    first_expr_diff(&actual.value, &expected.value, &level_map).unwrap_or_default()
                )
            };
            let msg = format!(
                "{}: mismatch (name_ok={name_ok} levels_ok={levels_ok} type_ok={type_ok} value_ok={value_ok} hints={:?} vs {:?} safety={:?} vs {:?} {diff})",
                expected.base.name.to_display_string(),
                actual.hints,
                expected.hints,
                actual.safety,
                expected.safety,
            );
            if self.first_mismatch.is_none() {
                self.first_mismatch = Some(msg.clone());
            }
            if self.samples.len() < 10 {
                self.samples.push(msg);
            }
        }
    }

    fn record_def(&mut self, actual: &DefinitionVal, expected: &DefinitionVal) {
        self.record_def_with_alpha_levels(actual, expected, false);
    }

    fn record_error(&mut self, label: &Name, detail: String) {
        self.population += 1;
        self.mismatches += 1;
        let msg = format!("{}: {detail}", label.to_display_string());
        if self.first_mismatch.is_none() {
            self.first_mismatch = Some(msg.clone());
        }
        if self.samples.len() < 10 {
            self.samples.push(msg);
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
        for extra in self.samples.iter().skip(1) {
            println!("    sample: {extra}");
        }
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

fn module_name_from_path(lib_root: &Path, olean_path: &Path) -> Option<Name> {
    let rel = olean_path.strip_prefix(lib_root).ok()?;
    let no_ext = rel.with_extension("");
    let mut name = Name::anonymous();
    for comp in no_ext.components() {
        let s = comp.as_os_str().to_str()?;
        name = Name::str(name, s);
    }
    (!name.is_anonymous()).then_some(name)
}

#[derive(Default)]
struct LoadedCorpus {
    exported_constants: BTreeMap<Name, ConstantInfo>,
    constants: BTreeMap<Name, ConstantInfo>,
    module_imports: BTreeMap<Name, Vec<Name>>,
    inductive_module: BTreeMap<Name, Name>,
    nce_module: Option<Name>,
    before_nce_in_own_module: BTreeSet<Name>,
}

impl LoadedCorpus {
    fn compute_modules_importing(&self, target: &Name) -> BTreeSet<Name> {
        let mut reverse: BTreeMap<Name, Vec<Name>> = BTreeMap::new();
        for (module, imports) in &self.module_imports {
            for imp in imports {
                reverse.entry(imp.clone()).or_default().push(module.clone());
            }
        }
        let mut reachable = BTreeSet::new();
        let mut work = vec![target.clone()];
        while let Some(cur) = work.pop() {
            if let Some(dependents) = reverse.get(&cur) {
                for dep in dependents {
                    if reachable.insert(dep.clone()) {
                        work.push(dep.clone());
                    }
                }
            }
        }
        reachable
    }
}

fn load_module_constants(lib_root: &Path, olean_path: &Path, corpus: &mut LoadedCorpus) {
    let mod_name = module_name_from_path(lib_root, olean_path);
    let server = olean_path.with_extension("olean.server");
    let private = olean_path.with_extension("olean.private");
    let Ok(base_bytes) = std::fs::read(olean_path) else {
        return;
    };
    let nce = Name::from_components(["noConfusionEnum"]);
    if let Ok(view) = OleanView::parse(&base_bytes) {
        if let Some(m) = &mod_name
            && let Ok(mdata) = view.module_data(WalkBudget::default())
        {
            corpus.module_imports.insert(
                m.clone(),
                mdata.imports.into_iter().map(|i| i.module).collect(),
            );
        }
        if let Ok(constants) =
            DeclDecoder::new(&view, WalkBudget::default()).decode_module_constants()
        {
            let has_nce = constants.iter().any(|info| info.name() == &nce);
            if has_nce {
                corpus.nce_module = mod_name.clone();
                let mut seen_nce = false;
                for info in &constants {
                    if info.name() == &nce {
                        seen_nce = true;
                    } else if !seen_nce && matches!(info, ConstantInfo::Induct(_)) {
                        corpus.before_nce_in_own_module.insert(info.name().clone());
                    }
                }
            }
            for info in constants {
                if let Some(m) = &mod_name
                    && matches!(info, ConstantInfo::Induct(_))
                {
                    corpus
                        .inductive_module
                        .insert(info.name().clone(), m.clone());
                }
                corpus.exported_constants.insert(info.name().clone(), info);
            }
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
            if let Some(m) = &mod_name
                && matches!(info, ConstantInfo::Induct(_))
            {
                corpus
                    .inductive_module
                    .entry(info.name().clone())
                    .or_insert_with(|| m.clone());
            }
            corpus.constants.insert(info.name().clone(), info);
        }
        return;
    }
    if let Ok(view) = OleanView::parse(&base_bytes)
        && let Ok(constants) =
            DeclDecoder::new(&view, WalkBudget::default()).decode_module_constants()
    {
        for info in constants {
            if let Some(m) = &mod_name
                && matches!(info, ConstantInfo::Induct(_))
            {
                corpus
                    .inductive_module
                    .entry(info.name().clone())
                    .or_insert_with(|| m.clone());
            }
            corpus.constants.insert(info.name().clone(), info);
        }
    }
}

fn course_families(
    constants: &BTreeMap<Name, ConstantInfo>,
    block: &[InductiveVal],
    recursor: &RecursorVal,
) -> Vec<InductiveVal> {
    let mut families = block.to_vec();
    let mut names: BTreeSet<Name> = block.iter().map(|f| f.base.name.clone()).collect();
    let mut seen = BTreeSet::new();
    let mut work = vec![&recursor.base.type_];
    while let Some(term) = work.pop() {
        if !seen.insert(term.allocation_identity()) {
            continue;
        }
        match term.node() {
            ExprNode::Const { name, .. } => {
                if !names.contains(name)
                    && let Some(ConstantInfo::Induct(family)) = constants.get(name)
                {
                    names.insert(name.clone());
                    families.push(family.clone());
                }
            }
            ExprNode::App { f, a } => work.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => work.extend([binder_type, body]),
            ExprNode::LetE {
                type_, value, body, ..
            } => work.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => work.push(expr),
            _ => {}
        }
    }
    families
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
    let mut corpus = LoadedCorpus::default();
    for path in &olean_files {
        load_module_constants(&lib_path, path, &mut corpus);
    }
    let modules_with_nce = corpus
        .nce_module
        .as_ref()
        .map(|m| corpus.compute_modules_importing(m))
        .unwrap_or_default();
    let LoadedCorpus {
        exported_constants,
        constants,
        inductive_module,
        nce_module,
        before_nce_in_own_module,
        ..
    } = corpus;
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
    let mut ctor_names: BTreeSet<Name> = BTreeSet::new();
    for (name, info) in &constants {
        if matches!(info, ConstantInfo::Ctor(_)) {
            ctor_names.insert(name.clone());
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

    // Inventory remaining derived families (inductive-child and constructor-child)
    // not yet covered by corpus-wide generators, plus unclassified constructor-child suffixes.
    #[derive(Default)]
    struct NotImplStats {
        count: usize,
        first: Option<(String, u64)>,
    }
    let mut not_impl: BTreeMap<&'static str, NotImplStats> = BTreeMap::new();
    let mut ctor_unclassified: BTreeMap<String, usize> = BTreeMap::new();
    let fnv1a_type = |info: &ConstantInfo| -> u64 {
        let repr = format!("{:?}", info.constant_val().type_);
        let mut h: u64 = 0xcbf29ce484222325;
        for b in repr.as_bytes() {
            h ^= u64::from(*b);
            h = h.wrapping_mul(0x100000001b3);
        }
        h
    };
    let mut record_not_impl = |family: &'static str, name: &Name, info: &ConstantInfo| {
        let entry = not_impl.entry(family).or_default();
        entry.count += 1;
        if entry.first.is_none() {
            entry.first = Some((name.to_display_string(), fnv1a_type(info)));
        }
    };
    for (name, info) in &constants {
        if matches!(info, ConstantInfo::Ctor(_)) {
            continue;
        }
        let parent = name.parent();
        let LeafView::Str(leaf) = name.leaf_view() else {
            continue;
        };
        if ind_names.contains(&parent) {
            if leaf == "_sizeOf_inst" {
                record_not_impl("_sizeOf_inst", name, info);
            } else if leaf.starts_with("_sizeOf_") {
                record_not_impl("_sizeOf_*", name, info);
            } else if leaf == "inj" {
                record_not_impl("ind.inj", name, info);
            } else if leaf == "injEq" {
                record_not_impl("ind.injEq", name, info);
            }
        } else if ctor_names.contains(&parent) {
            match leaf {
                "elim" => {}
                "noConfusion" => record_not_impl("ctor.noConfusion", name, info),
                "inj" => record_not_impl("ctor.inj", name, info),
                "injEq" => record_not_impl("ctor.injEq", name, info),
                "_flat_ctor" => record_not_impl("ctor._flat_ctor", name, info),
                "sizeOf_spec" => record_not_impl("ctor.sizeOf_spec", name, info),
                other => *ctor_unclassified.entry(other.to_owned()).or_default() += 1,
            }
        }
    }

    let budget = generation_budget();
    let mut rec_on_tally = FamilyTally::default();
    let mut cases_on_tally = FamilyTally::default();
    let mut below_tally = FamilyTally::default();
    let mut brec_go_tally = FamilyTally::default();
    let mut brec_on_tally = FamilyTally::default();
    let mut ctor_idx_tally = FamilyTally::default();
    let mut to_ctor_idx_tally = FamilyTally::default();
    let mut ctor_elim_type_tally = FamilyTally::default();
    let mut ctor_elim_tally = FamilyTally::default();
    let mut constructor_elim_tally = FamilyTally::default();
    let mut no_confusion_type_tally = FamilyTally::default();
    let mut no_confusion_tally = FamilyTally::default();
    // Per-shape (single / mutual / nested) parity totals across all 12 implemented generators.
    let mut shape_totals: [(usize, usize, usize); 3] = [(0, 0, 0); 3];

    for ind_name in &ind_names {
        let Some(ConstantInfo::Induct(inductive)) = constants.get(ind_name) else {
            continue;
        };
        let shape_idx = if inductive.num_nested > 0 {
            2
        } else if inductive.all.len() > 1 {
            1
        } else {
            0
        };
        let snap_totals = |tallies: [&FamilyTally; 12]| -> (usize, usize, usize) {
            let pop = tallies.iter().map(|t| t.population).sum();
            let id = tallies.iter().map(|t| t.identical).sum();
            let mm = tallies.iter().map(|t| t.mismatches).sum();
            (pop, id, mm)
        };
        let before = snap_totals([
            &rec_on_tally,
            &cases_on_tally,
            &below_tally,
            &brec_go_tally,
            &brec_on_tally,
            &ctor_idx_tally,
            &to_ctor_idx_tally,
            &ctor_elim_type_tally,
            &ctor_elim_tally,
            &constructor_elim_tally,
            &no_confusion_type_tally,
            &no_confusion_tally,
        ]);
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

        // below / brecOn.go / brecOn (primary and nested `_1.._k`).
        // The pin only generates course-of-values auxiliaries for recursive
        // inductives (`inductive.is_rec`); e.g. `Lean.Elab.Structural.IndGroupInst.brecOn`
        // is an ordinary user function on a non-recursive structure.
        let nested_max = if inductive.all.first() == Some(ind_name) {
            inductive.num_nested
        } else {
            0
        };
        for nest_idx in 0..=nested_max {
            if !inductive.is_rec {
                break;
            }
            let suffix = if nest_idx == 0 {
                String::new()
            } else {
                format!("_{nest_idx}")
            };
            let below_name = Name::str(ind_name.clone(), format!("below{suffix}"));
            let brec_name = Name::str(ind_name.clone(), format!("brecOn{suffix}"));
            let go_name = Name::str(brec_name.clone(), "go");
            let exp_below = match constants.get(&below_name) {
                Some(ConstantInfo::Defn(def)) => Some(def),
                _ => None,
            };
            let exp_brec = match constants.get(&brec_name) {
                Some(ConstantInfo::Defn(def)) => Some(def),
                _ => None,
            };
            let exp_go = match constants.get(&go_name) {
                Some(ConstantInfo::Defn(def)) => Some(def),
                _ => None,
            };
            if exp_below.is_none() && exp_brec.is_none() && exp_go.is_none() {
                continue;
            }
            let r_name = Name::str(ind_name.clone(), format!("rec{suffix}"));
            let Some(ConstantInfo::Rec(rec)) = constants.get(&r_name) else {
                if exp_below.is_some() {
                    below_tally.record_error(&below_name, "missing matching recursor".to_owned());
                }
                continue;
            };
            let fams = course_families(&constants, &block, rec);
            if let Some(exp) = exp_below {
                match below_declaration(rec, &fams, budget) {
                    Ok(act) => below_tally.record_def(&act, exp),
                    Err(e) => below_tally.record_error(&below_name, e.to_string()),
                }
            }
            if exp_go.is_some() || exp_brec.is_some() {
                match brec_on_declarations(rec, &fams, budget) {
                    Ok([act_go, act_brec]) => {
                        if let Some(exp) = exp_go {
                            brec_go_tally.record_def(&act_go, exp);
                        }
                        if let Some(exp) = exp_brec {
                            brec_on_tally.record_def(&act_brec, exp);
                        }
                    }
                    Err(e) => {
                        if exp_brec.is_some() {
                            brec_on_tally.record_error(&brec_name, e.to_string());
                        }
                    }
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

        // noConfusionType / noConfusion
        let nct_name = Name::str(ind_name.clone(), "noConfusionType");
        let nc_name = Name::str(ind_name.clone(), "noConfusion");
        let exp_nct = match constants.get(&nct_name) {
            Some(ConstantInfo::Defn(def)) => Some(def),
            _ => None,
        };
        let exp_nc = match constants.get(&nc_name) {
            Some(ConstantInfo::Defn(def)) => Some(def),
            _ => None,
        };
        if (exp_nct.is_some() || exp_nc.is_some())
            && let Some(cases_on) = cases_on_opt
        {
            let use_enum_helper = match inductive_module.get(ind_name) {
                Some(m) if Some(m) == nce_module.as_ref() => {
                    !before_nce_in_own_module.contains(ind_name)
                }
                Some(m) => modules_with_nce.contains(m),
                None => false,
            };
            match no_confusion_declarations(
                inductive,
                &ctors,
                cases_on,
                use_enum_helper,
                budget,
                |n| constants.get(n),
            ) {
                Ok(Some(cands)) => {
                    if let Some(exp) = exp_nct {
                        no_confusion_type_tally.record_def_with_alpha_levels(
                            &cands.no_confusion_type,
                            exp,
                            cands.is_enum_construction,
                        );
                    }
                    if let Some(exp) = exp_nc {
                        no_confusion_tally.record_def_with_alpha_levels(
                            &cands.no_confusion,
                            exp,
                            cands.is_enum_construction,
                        );
                    }
                }
                Ok(None) => {
                    if exp_nct.is_some() {
                        no_confusion_type_tally.record_error(
                            &nct_name,
                            "generator returned None for pin noConfusionType".to_owned(),
                        );
                    }
                }
                Err(e) => {
                    if exp_nct.is_some() {
                        no_confusion_type_tally.record_error(&nct_name, e.to_string());
                    }
                }
            }
        }
        let after = snap_totals([
            &rec_on_tally,
            &cases_on_tally,
            &below_tally,
            &brec_go_tally,
            &brec_on_tally,
            &ctor_idx_tally,
            &to_ctor_idx_tally,
            &ctor_elim_type_tally,
            &ctor_elim_tally,
            &constructor_elim_tally,
            &no_confusion_type_tally,
            &no_confusion_tally,
        ]);
        shape_totals[shape_idx].0 += after.0 - before.0;
        shape_totals[shape_idx].1 += after.1 - before.1;
        shape_totals[shape_idx].2 += after.2 - before.2;
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
    below_tally.print("below");
    brec_go_tally.print("brecOn.go");
    brec_on_tally.print("brecOn");
    ctor_idx_tally.print("ctorIdx");
    to_ctor_idx_tally.print("toCtorIdx");
    ctor_elim_type_tally.print("ctorElimType");
    ctor_elim_tally.print("ctorElim");
    constructor_elim_tally.print("ctor.elim");
    no_confusion_type_tally.print("noConfusionType");
    no_confusion_tally.print("noConfusion");

    println!("=== PARITY BY INDUCTIVE SHAPE (12 IMPLEMENTED GENERATORS) ===");
    for (label, (pop, id, mm)) in [
        ("single", shape_totals[0]),
        ("mutual", shape_totals[1]),
        ("nested", shape_totals[2]),
    ] {
        println!("  {label:<16} identical={id:>5}/{pop:<5}  mismatches={mm:>4}");
    }

    println!("=== REMAINING DERIVED FAMILIES (MEASURED NOT-IMPLEMENTED IN PROBE) ===");
    for (family, stats) in &not_impl {
        let first_str = match &stats.first {
            Some((name, digest)) => format!("first={name} (type_fnv1a={digest:016x})"),
            None => "first=none".to_owned(),
        };
        println!(
            "  {family:<16} identical=    0/{:<5}  status=not-implemented  {first_str}",
            stats.count
        );
    }

    println!("=== KNOWN DERIVED SUFFIX HISTOGRAM ===");
    let mut known_sorted: Vec<_> = known_suffixes.into_iter().collect();
    known_sorted.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    for (suffix, count) in known_sorted {
        println!("  {count:>5}  .{suffix}");
    }
    println!(
        "=== UNCLASSIFIED IMMEDIATE-CHILD SUFFIXES (distinct={}, showing top 25) ===",
        other_suffixes.len()
    );
    let mut other_sorted: Vec<_> = other_suffixes.into_iter().collect();
    other_sorted.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    for (suffix, count) in other_sorted.into_iter().take(25) {
        println!("  {count:>5}  .{suffix}");
    }
    println!(
        "=== UNCLASSIFIED CONSTRUCTOR-CHILD SUFFIXES (distinct={}, showing top 25) ===",
        ctor_unclassified.len()
    );
    let mut ctor_other_sorted: Vec<_> = ctor_unclassified.into_iter().collect();
    ctor_other_sorted.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    for (suffix, count) in ctor_other_sorted.into_iter().take(25) {
        println!("  {count:>5}  .<ctor>.{suffix}");
    }

    let floor_checks = [
        ("inductives", ind_names.len(), 2500usize),
        ("recOn", rec_on_tally.population, 2500),
        ("casesOn", cases_on_tally.population, 2500),
        ("below", below_tally.population, 200),
        ("brecOn.go", brec_go_tally.population, 200),
        ("brecOn", brec_on_tally.population, 200),
        ("ctorIdx", ctor_idx_tally.population, 2500),
        ("toCtorIdx", to_ctor_idx_tally.population, 150),
        ("ctorElimType", ctor_elim_type_tally.population, 450),
        ("ctorElim", ctor_elim_tally.population, 450),
        ("ctor.elim", constructor_elim_tally.population, 2000),
        ("noConfusionType", no_confusion_type_tally.population, 2500),
        ("noConfusion", no_confusion_tally.population, 2500),
    ];
    let mut floor_failures = Vec::new();
    for (label, observed, floor) in floor_checks {
        if observed < floor {
            floor_failures.push(format!("{label}: observed {observed} < floor {floor}"));
        }
    }
    if !floor_failures.is_empty() {
        eprintln!("ANTI-VACUITY FLOOR FAILURE: {}", floor_failures.join(", "));
    }

    let total_mismatches = rec_on_tally.mismatches
        + cases_on_tally.mismatches
        + below_tally.mismatches
        + brec_go_tally.mismatches
        + brec_on_tally.mismatches
        + ctor_idx_tally.mismatches
        + to_ctor_idx_tally.mismatches
        + ctor_elim_type_tally.mismatches
        + ctor_elim_tally.mismatches
        + constructor_elim_tally.mismatches
        + no_confusion_type_tally.mismatches
        + no_confusion_tally.mismatches;
    if (total_mismatches == 0 && floor_failures.is_empty()) || report_only {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    }
}
