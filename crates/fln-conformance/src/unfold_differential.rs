//! Declaration-level K1 vs pinned-Reference kernel unfold-count differential
//! (bead `fln-kernel-unfold-differential-tfvw`).
//!
//! Joins K1's `fln_kernel::observe_unfolds` histogram against the stock pinned
//! Reference kernel's `Kernel.Diagnostics.unfoldCounter` (collected by
//! `scripts/tribunal/unfold_counts.lean`), ranking shared declarations by
//! `K1 count / pin count` and separating one-sided unfolds.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use fln::{OleanDecodeLimits, decode_olean_artifact, decode_olean_module_artifacts};
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_env::constants::ConstantInfo;
use fln_env::environment::{Environment, ProvisionalEnvironment};
use fln_kernel::verdict::{Budget, Verdict};
use fln_kernel::{Declaration, UnfoldObservation};

/// Parsed unfold-count output from `scripts/tribunal/unfold_counts.lean`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PinUnfoldTable {
    pub module: String,
    pub declaration: String,
    pub verdict: String,
    pub wall_ns: u64,
    pub counts: BTreeMap<String, u64>,
}

/// One constant unfolded by both K1 and the Reference kernel.
#[derive(Debug, Clone, PartialEq)]
pub struct UnfoldDiffRow {
    pub name: String,
    pub k1_count: u64,
    pub pin_count: u64,
    pub ratio: f64,
}

/// Joined differential report comparing K1 unfold counts against the Reference.
#[derive(Debug, Clone, PartialEq)]
pub struct UnfoldDifferentialReport {
    /// Constants unfolded by both sides (positive counts), ranked descending by
    /// `k1_count / pin_count`, then `k1_count`, then `name`.
    pub shared_ranked: Vec<UnfoldDiffRow>,
    /// Constants unfolded only by K1 (pin count 0 or absent), ranked descending
    /// by `k1_count`, then `name`.
    pub k1_only: Vec<(String, u64)>,
    /// Constants unfolded only by the Reference (K1 count 0 or absent), ranked
    /// descending by `pin_count`, then `name`.
    pub pin_only: Vec<(String, u64)>,
    pub max_shared_ratio: f64,
    pub total_k1_unfolds: u64,
    pub total_pin_unfolds: u64,
}

impl UnfoldDifferentialReport {
    /// Format a compact deterministic summary for logs and bead evidence comments.
    pub fn render_top(&self, limit: usize) -> String {
        let mut out = String::new();
        out.push_str(&format!(
            "total_k1={} total_pin={} shared={} k1_only={} pin_only={} max_shared_ratio={:.3}\n",
            self.total_k1_unfolds,
            self.total_pin_unfolds,
            self.shared_ranked.len(),
            self.k1_only.len(),
            self.pin_only.len(),
            self.max_shared_ratio,
        ));
        for row in self.shared_ranked.iter().take(limit) {
            out.push_str(&format!(
                "  shared  {:>10.3}x  k1={:<10} pin={:<10} {}\n",
                row.ratio, row.k1_count, row.pin_count, row.name
            ));
        }
        for (name, count) in self.k1_only.iter().take(limit) {
            out.push_str(&format!(
                "  k1_only {:>10}   k1={:<10} pin=0          {}\n",
                "inf", count, name
            ));
        }
        for (name, count) in self.pin_only.iter().take(limit) {
            out.push_str(&format!(
                "  pin_only {:>9}   k1=0          pin={:<10} {}\n",
                "0.000x", count, name
            ));
        }
        out
    }
}

/// Join K1 and Reference unfold tables by declaration name and rank shared rows
/// by descending `k1_count / pin_count`. Zero-count entries are treated as absent
/// on that side (preventing division by zero or `NaN`).
pub fn join_and_rank(
    k1: &BTreeMap<String, u64>,
    pin: &BTreeMap<String, u64>,
) -> UnfoldDifferentialReport {
    let mut all_names: BTreeSet<&str> = BTreeSet::new();
    let mut total_k1 = 0_u64;
    let mut total_pin = 0_u64;
    for (k, &v) in k1 {
        total_k1 = total_k1.saturating_add(v);
        if v > 0 {
            all_names.insert(k.as_str());
        }
    }
    for (k, &v) in pin {
        total_pin = total_pin.saturating_add(v);
        if v > 0 {
            all_names.insert(k.as_str());
        }
    }

    let mut shared_ranked = Vec::new();
    let mut k1_only = Vec::new();
    let mut pin_only = Vec::new();

    for name in all_names {
        let k1_c = k1.get(name).copied().unwrap_or(0);
        let pin_c = pin.get(name).copied().unwrap_or(0);
        match (k1_c > 0, pin_c > 0) {
            (true, true) => {
                let ratio = (k1_c as f64) / (pin_c as f64);
                shared_ranked.push(UnfoldDiffRow {
                    name: name.to_owned(),
                    k1_count: k1_c,
                    pin_count: pin_c,
                    ratio,
                });
            }
            (true, false) => k1_only.push((name.to_owned(), k1_c)),
            (false, true) => pin_only.push((name.to_owned(), pin_c)),
            (false, false) => {}
        }
    }

    shared_ranked.sort_by(|a, b| {
        b.ratio
            .total_cmp(&a.ratio)
            .then_with(|| b.k1_count.cmp(&a.k1_count))
            .then_with(|| a.name.cmp(&b.name))
    });
    k1_only.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
    pin_only.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));

    let max_shared_ratio = shared_ranked.first().map_or(1.0, |row| row.ratio);
    UnfoldDifferentialReport {
        shared_ranked,
        k1_only,
        pin_only,
        max_shared_ratio,
        total_k1_unfolds: total_k1,
        total_pin_unfolds: total_pin,
    }
}

/// Convert K1's `Name`-keyed unfold map into display-string keys matching Lean's
/// `Name.toString`.
pub fn display_counts(counts: &BTreeMap<Name, u64>) -> BTreeMap<String, u64> {
    counts
        .iter()
        .map(|(name, &count)| (name.to_display_string(), count))
        .collect()
}

/// Parse stdout emitted by `scripts/tribunal/unfold_counts.lean`.
pub fn parse_pin_unfold_output(stdout: &str) -> Result<PinUnfoldTable, String> {
    let mut module = String::new();
    let mut declaration = String::new();
    let mut verdict = String::new();
    let mut wall_ns = 0_u64;
    let mut expected_entries: Option<usize> = None;
    let mut counts = BTreeMap::new();
    let mut prev_name: Option<String> = None;

    for (line_no, raw) in stdout.lines().enumerate() {
        let line = raw.trim_end_matches('\r');
        if line.is_empty() {
            continue;
        }
        if let Some(rest) = line.strip_prefix("# ") {
            let (key, val) = rest
                .split_once('\t')
                .ok_or_else(|| format!("malformed header at line {}: {line:?}", line_no + 1))?;
            match key {
                "module" => module = val.to_owned(),
                "declaration" => declaration = val.to_owned(),
                "verdict" => verdict = val.to_owned(),
                "wall_ns" => {
                    wall_ns = val
                        .parse::<u64>()
                        .map_err(|e| format!("invalid wall_ns {val:?}: {e}"))?;
                }
                "entries" => {
                    expected_entries = Some(
                        val.parse::<usize>()
                            .map_err(|e| format!("invalid entries {val:?}: {e}"))?,
                    );
                }
                _ => {}
            }
            continue;
        }
        let (name, count_str) = line
            .split_once('\t')
            .ok_or_else(|| format!("malformed row at line {}: {line:?}", line_no + 1))?;
        let count = count_str
            .parse::<u64>()
            .map_err(|e| format!("invalid count {count_str:?} at line {}: {e}", line_no + 1))?;
        if let Some(prev) = &prev_name
            && name <= prev.as_str()
        {
            return Err(format!(
                "pin unfold output is not strictly sorted: {name:?} after {prev:?}"
            ));
        }
        prev_name = Some(name.to_owned());
        counts.insert(name.to_owned(), count);
    }

    if module.is_empty() || declaration.is_empty() || verdict.is_empty() {
        return Err("pin unfold output missing required header fields".to_owned());
    }
    if let Some(expected) = expected_entries
        && counts.len() != expected
    {
        return Err(format!(
            "pin unfold entry count mismatch: header said {expected}, parsed {}",
            counts.len()
        ));
    }
    Ok(PinUnfoldTable {
        module,
        declaration,
        verdict,
        wall_ns,
        counts,
    })
}

/// Run the stock pinned Reference `lean` binary on `scripts/tribunal/unfold_counts.lean`
/// for one `(module, declaration)` pair.
pub fn run_pin_unfold_counts(
    workspace_root: &Path,
    pin_lean: &Path,
    lean_path: &str,
    module: &str,
    declaration: &str,
) -> Result<PinUnfoldTable, String> {
    let script = workspace_root.join("scripts/tribunal/unfold_counts.lean");
    if !script.is_file() {
        return Err(format!("missing pin script {}", script.display()));
    }
    let output = Command::new(pin_lean)
        .arg("--run")
        .arg(&script)
        .arg(module)
        .arg(declaration)
        .env("LEAN_PATH", lean_path)
        .output()
        .map_err(|e| format!("failed to spawn {}: {e}", pin_lean.display()))?;
    if !output.status.success() {
        return Err(format!(
            "pin unfold_counts failed (exit {:?}) for {module}::{declaration}:\nstdout: {}\nstderr: {}",
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        ));
    }
    let stdout = String::from_utf8(output.stdout)
        .map_err(|e| format!("pin unfold_counts stdout was not UTF-8: {e}"))?;
    parse_pin_unfold_output(&stdout)
}

/// Result of running K1's unfold observer over one declaration from a module's
/// `.olean` import closure.
#[derive(Debug)]
pub struct K1UnfoldRun {
    pub module: String,
    pub declaration: String,
    pub observation: UnfoldObservation,
    pub wall: Duration,
}

impl K1UnfoldRun {
    pub fn display_counts(&self) -> BTreeMap<String, u64> {
        display_counts(&self.observation.unfolds)
    }

    pub fn verdict_label(&self) -> &'static str {
        match &self.observation.outcome {
            Outcome::Complete(Verdict::Accepted { .. }) => "accepted",
            Outcome::Complete(Verdict::Rejected { .. }) => "rejected",
            Outcome::Inconclusive(_) => "inconclusive",
            Outcome::InternalFault(_) => "internal-fault",
        }
    }
}

fn find_olean_in_roots(roots: &[PathBuf], module: &Name) -> Option<PathBuf> {
    let rel = module.to_display_string().replace('.', "/") + ".olean";
    for root in roots {
        let candidate = root.join(&rel);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

fn decode_module_from_roots(
    roots: &[PathBuf],
    module: &Name,
) -> Result<(Vec<Name>, Vec<ConstantInfo>), String> {
    let path = find_olean_in_roots(roots, module).ok_or_else(|| {
        format!(
            "could not locate {}.olean across {} search roots",
            module.to_display_string(),
            roots.len()
        )
    })?;
    let primary =
        std::fs::read(&path).map_err(|e| format!("failed to read {}: {e}", path.display()))?;
    let server_path = path.with_extension("olean.server");
    let private_path = path.with_extension("olean.private");
    let server = if server_path.is_file() {
        Some(
            std::fs::read(&server_path)
                .map_err(|e| format!("failed to read {}: {e}", server_path.display()))?,
        )
    } else {
        None
    };
    let private = if private_path.is_file() {
        Some(
            std::fs::read(&private_path)
                .map_err(|e| format!("failed to read {}: {e}", private_path.display()))?,
        )
    } else {
        None
    };
    let decoded = match (server.as_deref(), private.as_deref()) {
        (Some(s), Some(p)) => {
            let total = primary.len() + s.len() + p.len();
            decode_olean_module_artifacts(&primary, s, p, OleanDecodeLimits::new(total))
        }
        _ => decode_olean_artifact(&primary, OleanDecodeLimits::new(primary.len())),
    }
    .map_err(|e| format!("failed to decode {}: {e}", path.display()))?;
    let imports = decoded
        .module
        .imports
        .into_iter()
        .map(|imp| imp.module)
        .collect();
    Ok((imports, decoded.constants))
}

fn constant_to_declaration(info: &ConstantInfo) -> Result<Declaration, String> {
    match info {
        ConstantInfo::Axiom(v) => Ok(Declaration::Axiom(v.clone())),
        ConstantInfo::Defn(v) => Ok(Declaration::Defn(v.clone())),
        ConstantInfo::Thm(v) => Ok(Declaration::Thm(v.clone())),
        ConstantInfo::Opaque(v) => Ok(Declaration::Opaque(v.clone())),
        other => Err(format!(
            "unsupported declaration kind for single-decl unfold probe: {}",
            other.name().to_display_string()
        )),
    }
}

fn collect_expr_consts(expr: &fln_core::expr::Expr, out: &mut BTreeSet<Name>) {
    let mut stack = vec![expr];
    let mut seen: std::collections::HashSet<usize> = std::collections::HashSet::new();
    while let Some(e) = stack.pop() {
        let ptr = e.allocation_identity();
        if !seen.insert(ptr) {
            continue;
        }
        match e.node() {
            fln_core::expr::ExprNode::Const { name, .. } => {
                out.insert(name.clone());
            }
            fln_core::expr::ExprNode::App { f, a } => {
                stack.push(f);
                stack.push(a);
            }
            fln_core::expr::ExprNode::Lam {
                binder_type, body, ..
            }
            | fln_core::expr::ExprNode::ForallE {
                binder_type, body, ..
            } => {
                stack.push(binder_type);
                stack.push(body);
            }
            fln_core::expr::ExprNode::LetE {
                type_, value, body, ..
            } => {
                stack.push(type_);
                stack.push(value);
                stack.push(body);
            }
            fln_core::expr::ExprNode::Proj {
                struct_name, expr, ..
            } => {
                out.insert(struct_name.clone());
                stack.push(expr);
            }
            fln_core::expr::ExprNode::MData { expr, .. } => {
                stack.push(expr);
            }
            fln_core::expr::ExprNode::BVar { .. }
            | fln_core::expr::ExprNode::FVar { .. }
            | fln_core::expr::ExprNode::MVar { .. }
            | fln_core::expr::ExprNode::Sort { .. }
            | fln_core::expr::ExprNode::Lit { .. } => {}
        }
    }
}

fn collect_constant_refs(info: &ConstantInfo) -> BTreeSet<Name> {
    let mut refs = BTreeSet::new();
    collect_expr_consts(&info.constant_val().type_, &mut refs);
    match info {
        ConstantInfo::Defn(v) => collect_expr_consts(&v.value, &mut refs),
        ConstantInfo::Thm(v) => collect_expr_consts(&v.value, &mut refs),
        ConstantInfo::Opaque(v) => collect_expr_consts(&v.value, &mut refs),
        ConstantInfo::Rec(v) => {
            for rule in &v.rules {
                collect_expr_consts(&rule.rhs, &mut refs);
            }
        }
        _ => {}
    }
    refs
}

fn topo_order_constants(constants: &[ConstantInfo]) -> Vec<usize> {
    let by_name: BTreeMap<&Name, usize> = constants
        .iter()
        .enumerate()
        .map(|(i, c)| (c.name(), i))
        .collect();
    let deps: Vec<Vec<usize>> = constants
        .iter()
        .enumerate()
        .map(|(i, c)| {
            collect_constant_refs(c)
                .into_iter()
                .filter_map(|n| by_name.get(&n).copied())
                .filter(|&j| j != i)
                .collect()
        })
        .collect();
    let mut state = vec![0_u8; constants.len()]; // 0=unvisited, 1=visiting, 2=done
    let mut order = Vec::with_capacity(constants.len());
    enum Frame {
        Enter(usize),
        Exit(usize),
    }
    for start in 0..constants.len() {
        if state[start] != 0 {
            continue;
        }
        let mut stack = vec![Frame::Enter(start)];
        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Enter(u) => {
                    if state[u] != 0 {
                        continue;
                    }
                    state[u] = 1;
                    stack.push(Frame::Exit(u));
                    for &v in deps[u].iter().rev() {
                        if state[v] == 0 {
                            stack.push(Frame::Enter(v));
                        }
                    }
                }
                Frame::Exit(u) => {
                    state[u] = 2;
                    order.push(u);
                }
            }
        }
    }
    order
}

/// Per-declaration K1 step summary returned by [`LoadedOleanModule::scan_declarations`].
#[derive(Debug, Clone)]
pub struct DeclStepScanRow {
    pub name: String,
    pub verdict: &'static str,
    pub steps_used: u64,
    pub wall: Duration,
}

/// Decoded `.olean` module plus its deduplicated transitive import environment
/// (loaded once in a single batched `ProvisionalEnvironment` allocation for
/// fast multi-declaration scanning and unfold observation).
pub struct LoadedOleanModule {
    pub module: String,
    imports_env: ProvisionalEnvironment,
    constants: Vec<ConstantInfo>,
}

impl LoadedOleanModule {
    /// Load `module` and its transitive `.olean` import closure from `roots`.
    pub fn load(roots: &[PathBuf], module: &str) -> Result<Self, String> {
        let target_module = Name::from_components(module.split('.'));

        let mut visited: BTreeSet<Name> = BTreeSet::new();
        let mut topo_imports: Vec<Vec<ConstantInfo>> = Vec::new();
        let mut target_constants: Option<Vec<ConstantInfo>> = None;

        enum Frame {
            Enter(Name),
            Exit(Name, Vec<ConstantInfo>),
        }
        let mut stack = vec![Frame::Enter(target_module.clone())];
        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Enter(mod_name) => {
                    if !visited.insert(mod_name.clone()) {
                        continue;
                    }
                    let (imports, constants) = decode_module_from_roots(roots, &mod_name)?;
                    stack.push(Frame::Exit(mod_name, constants));
                    for imp in imports.into_iter().rev() {
                        if !visited.contains(&imp) {
                            stack.push(Frame::Enter(imp));
                        }
                    }
                }
                Frame::Exit(mod_name, constants) => {
                    if mod_name == target_module {
                        target_constants = Some(constants);
                    } else {
                        topo_imports.push(constants);
                    }
                }
            }
        }

        let constants = target_constants
            .ok_or_else(|| format!("target module {module} missing from decoded closure"))?;

        let mut all_imports = Vec::new();
        let mut seen = BTreeSet::new();
        for mod_constants in topo_imports {
            for info in mod_constants {
                if seen.insert(info.name().clone()) {
                    all_imports.push(info);
                }
            }
        }
        let mut imports_env = ProvisionalEnvironment::from_admitted(Environment::new());
        if !all_imports.is_empty() {
            imports_env = imports_env
                .assume_constants(&all_imports)
                .map_err(|e| format!("failed to populate diagnostic import env: {e:?}"))?;
        }

        Ok(Self {
            module: module.to_owned(),
            imports_env,
            constants,
        })
    }

    /// Number of constants declared in this module.
    pub fn declaration_count(&self) -> usize {
        self.constants.len()
    }

    /// Run `fln_kernel::observe_unfolds` on one named declaration in this module.
    pub fn observe_declaration(
        &self,
        declaration: &str,
        budget: Budget,
        force_left_delta: bool,
    ) -> Result<K1UnfoldRun, String> {
        let target_decl_name = Name::from_components(declaration.split('.'));
        let target_pos = self
            .constants
            .iter()
            .position(|c| c.name() == &target_decl_name)
            .ok_or_else(|| {
                format!(
                    "declaration {declaration} not found in module {}",
                    self.module
                )
            })?;
        let target_info = self.constants[target_pos].clone();
        let decl = constant_to_declaration(&target_info)?;

        let mut prereqs = Vec::new();
        let mut seen_prereq = BTreeSet::new();
        for info in &self.constants {
            if info.name() == &target_decl_name {
                continue;
            }
            if !self.imports_env.contains(info.name()) && seen_prereq.insert(info.name().clone()) {
                prereqs.push(info.clone());
            }
        }
        let env = if prereqs.is_empty() {
            self.imports_env.clone()
        } else {
            self.imports_env
                .assume_constants(&prereqs)
                .map_err(|e| format!("failed to populate module prerequisites: {e:?}"))?
        };

        let started = Instant::now();
        let observation = fln_kernel::observe_unfolds(
            env.as_check_environment(),
            &decl,
            budget,
            force_left_delta,
        );
        let wall = started.elapsed();

        Ok(K1UnfoldRun {
            module: self.module.clone(),
            declaration: declaration.to_owned(),
            observation,
            wall,
        })
    }

    /// Check every individually checkable declaration (`Axiom`, `Defn`, `Thm`,
    /// `Opaque`) in this module under `budget`, returning rows sorted descending
    /// by `steps_used` (with inconclusive/stopped rows ranked first).
    pub fn scan_declarations(&self, budget: Budget) -> Result<Vec<DeclStepScanRow>, String> {
        let mut rows = Vec::new();
        // Progressively populate module constants in intra-module topological
        // dependency order so every declaration sees its prerequisites.
        let mut running_env = self.imports_env.clone();
        for idx in topo_order_constants(&self.constants) {
            let info = &self.constants[idx];
            let decl_name = info.name().to_display_string();
            let already = running_env.contains(info.name());
            if !already && let Ok(decl) = constant_to_declaration(info) {
                let started = Instant::now();
                let outcome = fln_kernel::check(running_env.as_check_environment(), &decl, budget);
                let wall = started.elapsed();
                let (verdict, steps_used) = match &outcome {
                    Outcome::Complete(Verdict::Accepted { consumption, .. }) => {
                        ("accepted", consumption.steps_used)
                    }
                    Outcome::Complete(Verdict::Rejected { consumption, .. }) => {
                        ("rejected", consumption.steps_used)
                    }
                    Outcome::Inconclusive(_) => ("inconclusive", budget.steps),
                    Outcome::InternalFault(_) => ("internal-fault", budget.steps),
                };
                rows.push(DeclStepScanRow {
                    name: decl_name,
                    verdict,
                    steps_used,
                    wall,
                });
            }
            if !already {
                running_env = running_env
                    .assume_constants(std::slice::from_ref(info))
                    .map_err(|e| {
                        format!(
                            "failed to extend diagnostic env with {}: {e:?}",
                            info.name().to_display_string()
                        )
                    })?;
            }
        }
        rows.sort_by(|a, b| {
            let a_stuck = a.verdict != "accepted";
            let b_stuck = b.verdict != "accepted";
            b_stuck
                .cmp(&a_stuck)
                .then_with(|| b.steps_used.cmp(&a.steps_used))
                .then_with(|| a.name.cmp(&b.name))
        });
        Ok(rows)
    }
}

/// Load `module`'s transitive `.olean` import closure plus every prerequisite
/// declaration in `module` into a non-authoritative [`ProvisionalEnvironment`],
/// then run [`fln_kernel::observe_unfolds`] on `declaration`.
///
/// This is a diagnostic Tribunal path only: the provisional environment never
/// mints admission tokens or leaves the process.
pub fn run_k1_unfold_counts_for_olean_module(
    roots: &[PathBuf],
    module: &str,
    declaration: &str,
    budget: Budget,
    force_left_delta: bool,
) -> Result<K1UnfoldRun, String> {
    let loaded = LoadedOleanModule::load(roots, module)?;
    loaded.observe_declaration(declaration, budget, force_left_delta)
}
