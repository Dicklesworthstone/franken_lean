//! G0-2 seed: the kernel differential replay rig (bead franken_lean-z6c,
//! plan §22.1-2, §18 kernel differential lane).
//!
//! A REAL Reference module — `Init.Prelude`, the import-free root of the
//! entire library — is decoded from its `.olean` (statements AND proofs,
//! bit-level identity cross-checks on) and replayed through the one
//! authority, `fln_kernel::check`, declaration by declaration in module
//! order. The Reference kernel accepted every one of these declarations when
//! it produced the olean, so:
//!
//!   - `Accepted` = verdict agreement with the Reference;
//!   - `Inconclusive` = honest exhaustion, typed (FL-INV-07);
//!   - `Rejected` = a DIVERGENCE — either a K1 gap (expected classes are
//!     pinned below and re-triaged whenever the census moves) or a soundness
//!     finding (immediately fatal here).
//!
//! Every declaration kind in the module is kernel-checked (bead
//! franken_lean-ap6): inductive blocks as whole units under KR-6xx/7xx/8xx
//! with recursor regeneration, quotients under KR-95x, definitions of every
//! safety level under the pin's add_definition split. The one typed
//! limitation: a nested block (Lean.Syntax) admits under the partial ruleset
//! (no positivity, no regeneration) and is surfaced by the census.
//!
//! Evidence discipline (the ap6 acceptance contract): the replay runs a
//! deterministic {1, 8, 32} worker-thread matrix. Environment construction is
//! canonical (module-order Kahn) and shared; each unit is checked against the
//! O(1) environment snapshot it would see in the sequential replay, so the
//! authoritative verdict stream — classes, diagnostics, and consumption — is
//! schedule-independent by construction, and the matrix PROVES it byte-equal
//! at every width. Machine rows go to stdout as schema-versioned NDJSON
//! (`fln.e2e.kernel-admission`/`fln.e2e.kernel-admission-fault`, validated by
//! `scripts/evidence.py validate-kernel-admission`); human logs stay on
//! stderr — the two streams must never merge.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::PathBuf;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use fln_core::diag::{ResourceReason, StructuralUnit};
use fln_core::expr::{BinderInfo, Expr, ExprNode};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::{InconclusiveCause, Outcome, ResourceUsage};
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use fln_env::decl_closure::{
    self, DeclClosureBudget, DeclClosureInput, DeclClosureStatus, MissingConstantFinding,
};
use fln_env::environment::Environment;
use fln_hash::domain::{Domain, hash};
use fln_kernel::Declaration;
use fln_kernel::verdict::{Budget, Verdict};
use fln_olean::decl::DeclDecoder;
use fln_olean::region::{OleanView, WalkBudget};

/// Bounded term-shape rendering for the `FLN_REPLAY_PROBE` lane (bead
/// fln-d4x): enough to see how a rejected declaration's value is compiled —
/// recursor application vs projections vs constructor eta — without dumping
/// full proof terms. Fuel-bounded recursion, safe on real Reference terms.
fn shape(e: &Expr, fuel: usize) -> String {
    if fuel == 0 {
        return "…".to_string();
    }
    match e.node() {
        ExprNode::BVar { idx } => format!("#{idx}"),
        ExprNode::FVar { .. } => "fvar".to_string(),
        ExprNode::MVar { .. } => "mvar".to_string(),
        ExprNode::Sort { .. } => "Sort".to_string(),
        ExprNode::Const { name, .. } => name.to_display_string(),
        ExprNode::App { .. } => {
            let mut args = Vec::new();
            let mut head = e.clone();
            while let ExprNode::App { f, a } = head.node() {
                args.push(a.clone());
                let next = f.clone();
                head = next;
            }
            args.reverse();
            let mut out = format!("({}", shape(&head, fuel - 1));
            for arg in &args {
                out.push(' ');
                out.push_str(&shape(arg, fuel - 1));
            }
            out.push(')');
            out
        }
        ExprNode::Lam {
            binder_type, body, ..
        } => format!(
            "(fun (_ : {}) => {})",
            shape(binder_type, fuel - 1),
            shape(body, fuel - 1)
        ),
        ExprNode::ForallE {
            binder_type, body, ..
        } => format!(
            "(forall (_ : {}), {})",
            shape(binder_type, fuel - 1),
            shape(body, fuel - 1)
        ),
        ExprNode::LetE { body, .. } => format!("(let _ := ..; {})", shape(body, fuel - 1)),
        ExprNode::MData { expr, .. } => shape(expr, fuel),
        ExprNode::Proj {
            struct_name,
            idx,
            expr,
        } => format!(
            "({}.{} {})",
            struct_name.to_display_string(),
            idx,
            shape(expr, fuel - 1)
        ),
        ExprNode::Lit { .. } => "lit".to_string(),
    }
}

/// Collect every `Const` name reachable in a term. Iterative: real Reference
/// proofs are deep enough to overflow a recursive walk.
fn const_refs(expr: &Expr, out: &mut HashSet<Name>) {
    let mut stack = vec![expr.clone()];
    while let Some(e) = stack.pop() {
        match e.node() {
            ExprNode::Const { name, .. } => {
                out.insert(name.clone());
            }
            ExprNode::App { f, a } => {
                stack.push(f.clone());
                stack.push(a.clone());
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                stack.push(binder_type.clone());
                stack.push(body.clone());
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                stack.push(type_.clone());
                stack.push(value.clone());
                stack.push(body.clone());
            }
            ExprNode::MData { expr, .. } => stack.push(expr.clone()),
            ExprNode::Proj { expr, .. } => stack.push(expr.clone()),
            _ => {}
        }
    }
}

/// The constants a declaration depends on: every `Const` in its type and
/// value, PLUS the structural name references that carry no `Const` node —
/// an inductive names its constructors, a constructor names its inductive,
/// a recursor names its rules' constructors. The projection rule resolves
/// `ind.ctors[0]` through the environment, so those edges are load-bearing:
/// omitting them replays a structure's projections before its constructor
/// exists and manufactures spurious `InvalidProjection` verdicts.
fn dependencies(info: &ConstantInfo) -> HashSet<Name> {
    let mut out = HashSet::new();
    const_refs(&info.constant_val().type_, &mut out);
    match info {
        ConstantInfo::Defn(v) => const_refs(&v.value, &mut out),
        ConstantInfo::Thm(v) => const_refs(&v.value, &mut out),
        ConstantInfo::Opaque(v) => const_refs(&v.value, &mut out),
        ConstantInfo::Ctor(v) => {
            out.insert(v.induct.clone());
        }
        ConstantInfo::Rec(v) => {
            for rule in &v.rules {
                out.insert(rule.ctor.clone());
                const_refs(&rule.rhs, &mut out);
            }
        }
        _ => {}
    }
    out
}

/// Replay order over admission UNITS: a unit is admitted only after every
/// unit owning a constant any of its members mention (Kahn, with stable
/// unit-creation-order tie-breaking so the replay is deterministic). Because
/// every declaration belongs to exactly one unit, dependency edges are direct
/// — the d4x frontier-transitive expansion is subsumed (a declaration that
/// applies `Membership.rec` has an edge to the `Membership` BLOCK unit, whose
/// own edges cover `outParam` before it). Units inside a dependency cycle
/// (self-referential generated equation lemmas) are emitted last, in unit
/// order, and reported.
fn unit_topological_order(
    infos: &[ConstantInfo],
    units: &[Vec<usize>],
) -> (Vec<usize>, Vec<usize>) {
    let mut owner: HashMap<Name, usize> = HashMap::new();
    for (u, members) in units.iter().enumerate() {
        for &m in members {
            owner.insert(infos[m].name().clone(), u);
        }
    }
    let deps: Vec<Vec<usize>> = units
        .iter()
        .enumerate()
        .map(|(u, members)| {
            let mut d: HashSet<usize> = HashSet::new();
            for &m in members {
                for name in dependencies(&infos[m]) {
                    if let Some(&j) = owner.get(&name)
                        && j != u
                    {
                        d.insert(j);
                    }
                }
            }
            let mut d: Vec<usize> = d.into_iter().collect();
            d.sort_unstable();
            d
        })
        .collect();
    let mut remaining: Vec<usize> = deps.iter().map(|d| d.len()).collect();
    let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); units.len()];
    for (i, d) in deps.iter().enumerate() {
        for &j in d {
            dependents[j].push(i);
        }
    }
    let mut ready: Vec<usize> = (0..units.len()).filter(|&i| remaining[i] == 0).collect();
    ready.reverse(); // pop() yields ascending unit order
    let mut order = Vec::with_capacity(units.len());
    while let Some(i) = ready.pop() {
        order.push(i);
        for &d in &dependents[i] {
            remaining[d] -= 1;
            if remaining[d] == 0 {
                ready.push(d);
            }
        }
        ready.sort_unstable_by(|a, b| b.cmp(a));
    }
    let placed: HashSet<usize> = order.iter().copied().collect();
    let cyclic: Vec<usize> = (0..units.len()).filter(|i| !placed.contains(i)).collect();
    (order, cyclic)
}

/// Classify a rejected declaration into its reduction-gap sub-family, for the
/// triage breakdown. Every family here type-checks only under a reduction rule
/// K1's bootstrap slice does not yet implement (bead franken_lean-zht
/// follow-ups): iota on recursors/matchers, projection reduction on structure
/// instances, or Nat/Fin literal reduction. Purely diagnostic — the soundness
/// argument (below) does not depend on this taxonomy being exhaustive.
fn reduction_gap_family(name: &Name) -> &'static str {
    let s = name.to_display_string();
    let last = s.rsplit('.').next().unwrap_or(&s);
    if matches!(
        last,
        "rec"
            | "recOn"
            | "casesOn"
            | "brecOn"
            | "below"
            | "ibelow"
            | "binductionOn"
            | "noConfusion"
            | "noConfusionType"
    ) || last.starts_with("rec_")
        || last.starts_with("below_")
    {
        "eliminator (iota)"
    } else if last == "go" || last.contains("brecOn") {
        "well-founded-recursion helper (iota)"
    } else if last.starts_with("match_") || last.contains(".match_") {
        "match-compiler auxiliary (iota)"
    } else if last == "elim" || last == "ctorElim" || s.contains(".elim") {
        "custom eliminator (iota)"
    } else if last.ends_with("_f") || last.ends_with("_sunfold") {
        "equation-lemma helper (iota)"
    } else if last.contains("decEq")
        || last.contains("DecidableEq")
        || s.contains("instDecidable")
        || last.contains("decEq")
    {
        "decidability instance (iota/proj)"
    } else if last.contains("ofNat") || last.contains("ofNatLT") || last.contains("ofNatAux") {
        "nat-literal arithmetic (nat-lit reduction)"
    } else {
        // monad projections/instances (ReaderT.*, EStateM.*, inst*) and the
        // remaining generated helpers — projection reduction on structures.
        "structure projection/instance (proj reduction)"
    }
}

/// The kernel `Declaration` for a singleton-unit constant. Definitions of
/// EVERY safety level check (bead franken_lean-ap6: unsafe definitions take
/// the pin's two-phase path, partial definitions the safe path). `None` only
/// for kinds with no admission rule yet (opaques — none in Init.Prelude).
fn as_declaration(info: &ConstantInfo) -> Option<Declaration> {
    match info {
        ConstantInfo::Axiom(v) => Some(Declaration::Axiom(v.clone())),
        ConstantInfo::Thm(v) => Some(Declaration::Thm(v.clone())),
        ConstantInfo::Defn(v) => Some(Declaration::Defn(v.clone())),
        _ => None,
    }
}

/// Locate the pinned Reference stdlib. Override with FLN_REFERENCE_LIB; the
/// elan-installed pin is the default. Absent toolchain = typed skip (the
/// checked-in C3 fixtures cover decode; this rig needs the full Prelude).
fn reference_lib() -> Option<PathBuf> {
    if let Ok(dir) = std::env::var("FLN_REFERENCE_LIB") {
        let p = PathBuf::from(dir);
        return p.is_dir().then_some(p);
    }
    let home = std::env::var("HOME").ok()?;
    let p = PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean");
    p.is_dir().then_some(p)
}

// ---------------------------------------------------------------------------
// Evidence machinery (bead franken_lean-ap6): prepared replays, the worker
// matrix, and the NDJSON rows the lane validator checks.
// ---------------------------------------------------------------------------

/// Minimal JSON string escaper for the NDJSON rows (closed universe: no serde).
fn json_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// One admission unit prepared for checking: its canonical position, the
/// declaration, and the O(1) environment snapshot it is checked against —
/// exactly the environment the sequential replay would present. Snapshots
/// make the verdict for every unit a pure function of (env, decl, budget),
/// independent of worker schedule: the deterministic-merge argument the
/// thread matrix then witnesses.
struct WorkItem {
    lead: Name,
    kind: &'static str,
    members: u64,
    env: Environment,
    decl: Declaration,
    info: ConstantInfo,
}

struct PreparedReplay {
    items: Vec<WorkItem>,
    unchecked: BTreeMap<&'static str, u64>,
    /// Blocks with nested auxiliaries — all admitted under the FULL ruleset
    /// (the partial path was retired by franken_lean-8ce).
    nested_full: u64,
    /// Declarations whose artifact cannot supply the dependency closure (bead
    /// franken_lean-artifact-incomplete-private-refs-sgt): typed
    /// `ArtifactIncomplete` findings in canonical order. These declarations are
    /// NOT kernel-checked, NOT counted as checked, NOT cacheable, and — the
    /// core prohibition — never enter the environment.
    artifact_incomplete: Vec<MissingConstantFinding>,
    final_env: Environment,
    decls_total: usize,
    units_total: usize,
    cyclic_leads: Vec<String>,
}

impl PreparedReplay {
    /// One finding per affected declaration (never per unit): the count IS the
    /// row count.
    fn artifact_incomplete_count(&self) -> u64 {
        self.artifact_incomplete.len() as u64
    }

    /// The canonical witness digest over the (already canonically ordered)
    /// artifact-incomplete findings.
    fn artifact_witness_hex(&self) -> String {
        decl_closure::witness_digest(&self.artifact_incomplete).to_hex()
    }
}

/// Build the admission units of a decoded module and walk them in canonical
/// (Kahn) order, snapshotting each unit's checking environment and admitting
/// every declaration — the deterministic phase every matrix width shares.
fn prepare_replay(infos: &[ConstantInfo]) -> PreparedReplay {
    let index_by_name: HashMap<Name, usize> = infos
        .iter()
        .enumerate()
        .map(|(i, info)| (info.name().clone(), i))
        .collect();
    let mut recs_by_block: HashMap<Name, Vec<usize>> = HashMap::new();
    for (i, info) in infos.iter().enumerate() {
        if let ConstantInfo::Rec(r) = info
            && let Some(leader) = r.all.first()
        {
            recs_by_block.entry(leader.clone()).or_default().push(i);
        }
    }
    #[derive(Clone, Copy, PartialEq)]
    enum UnitKind {
        Single,
        Block,
        Quot,
    }
    struct Unit {
        kind: UnitKind,
        members: Vec<usize>,
    }
    let mut units: Vec<Unit> = Vec::new();
    let mut quot_members: Vec<usize> = Vec::new();
    for (i, info) in infos.iter().enumerate() {
        match info {
            ConstantInfo::Quot(_) => quot_members.push(i),
            // Constructors and recursors are absorbed into their block's unit.
            ConstantInfo::Ctor(_) | ConstantInfo::Rec(_) => {}
            ConstantInfo::Induct(ind) => {
                // Only the block leader creates the unit (singleton blocks
                // throughout Init.Prelude; the general case follows `all`).
                if ind.all.first() != Some(&ind.base.name) {
                    continue;
                }
                let mut members: Vec<usize> = Vec::new();
                for type_name in &ind.all {
                    if let Some(&t) = index_by_name.get(type_name) {
                        members.push(t);
                        if let ConstantInfo::Induct(t_ind) = &infos[t] {
                            for ctor_name in &t_ind.ctors {
                                if let Some(&c) = index_by_name.get(ctor_name) {
                                    members.push(c);
                                }
                            }
                        }
                    }
                }
                if let Some(recs) = recs_by_block.get(&ind.base.name) {
                    members.extend(recs.iter().copied());
                }
                units.push(Unit {
                    kind: UnitKind::Block,
                    members,
                });
            }
            _ => units.push(Unit {
                kind: UnitKind::Single,
                members: vec![i],
            }),
        }
    }
    if !quot_members.is_empty() {
        units.push(Unit {
            kind: UnitKind::Quot,
            members: quot_members,
        });
    }
    let member_lists: Vec<Vec<usize>> = units.iter().map(|u| u.members.clone()).collect();
    let (order, cyclic) = unit_topological_order(infos, &member_lists);
    let cyclic_leads: Vec<String> = cyclic
        .iter()
        .map(|&u| infos[units[u].members[0]].name().to_display_string())
        .collect();
    eprintln!(
        "kernel_replay order: {} units over {} declarations \
         ({} topologically sorted, {} in dependency cycles replayed last)",
        units.len(),
        infos.len(),
        order.len(),
        cyclic.len()
    );

    let mut env = Environment::new();
    let mut items: Vec<WorkItem> = Vec::new();
    let mut unchecked: BTreeMap<&'static str, u64> = BTreeMap::new();
    let mut nested_full: u64 = 0;
    let mut artifact_incomplete: Vec<MissingConstantFinding> = Vec::new();
    let units_total = units.len();
    for u in order.into_iter().chain(cyclic) {
        let unit = &units[u];
        let info = infos[unit.members[0]].clone();
        let n_members = unit.members.len() as u64;
        let (kind_str, decl): (&'static str, Option<Declaration>) = match unit.kind {
            UnitKind::Single => ("single", as_declaration(&info)),
            UnitKind::Block => {
                let mut types = Vec::new();
                let mut ctors = Vec::new();
                let mut recursors = Vec::new();
                for &m in &unit.members {
                    match &infos[m] {
                        ConstantInfo::Induct(v) => types.push(v.clone()),
                        ConstantInfo::Ctor(v) => ctors.push(v.clone()),
                        ConstantInfo::Rec(v) => recursors.push(v.clone()),
                        _ => {}
                    }
                }
                if types.iter().any(|t| t.num_nested > 0) {
                    nested_full += 1;
                }
                (
                    "block",
                    Some(Declaration::Inductive(fln_kernel::InductiveBlock {
                        types,
                        ctors,
                        recursors,
                    })),
                )
            }
            UnitKind::Quot => {
                let mut decls = Vec::new();
                for &m in &unit.members {
                    if let ConstantInfo::Quot(v) = &infos[m] {
                        decls.push(v.clone());
                    }
                }
                ("quot", Some(Declaration::Quotient(decls)))
            }
        };
        let Some(decl) = decl else {
            // No admission rule for this kind yet (opaques): typed limitation,
            // counted per kind — never a silent pass.
            for &m in &unit.members {
                *unchecked.entry(infos[m].kind_name()).or_default() += 1;
                env = env
                    .add_decl(infos[m].clone())
                    .expect("one-name law over Prelude");
            }
            continue;
        };
        // Artifact-incomplete (bead franken_lean-artifact-incomplete-private-
        // refs-sgt, upgrading the franken_lean-ap6 counter to a typed outcome):
        // non-safe implementation helpers (`._unsafe_rec`/`._override`)
        // reference PRIVATE auxiliaries (`.match_1`, `._proof_N`) that the
        // pin's own serializer does NOT include in the module's constants
        // array — their checking context was transient elaboration state, and
        // the Reference itself never re-checks imports
        // (`lean_add_decl_without_checking`). The closure census produces a
        // typed `ArtifactIncomplete` finding per declaration with its exact
        // missing references; the declarations are NOT kernel-checked, NOT
        // cacheable, and never enter the environment (cascade census: nothing
        // else in the module references them, so exclusion is closed).
        if let ConstantInfo::Defn(d) = &info
            && d.safety != DefinitionSafety::Safe
        {
            let census_input = [DeclClosureInput {
                name: info.name().clone(),
                safety: d.safety,
                dependencies: dependencies(&info).into_iter().collect(),
            }];
            let status = decl_closure::classify_closures(
                &census_input,
                |name| index_by_name.contains_key(name) || env.find(name).is_some(),
                DeclClosureBudget::DEFAULT,
                || false,
            );
            match status {
                DeclClosureStatus::Complete => {}
                DeclClosureStatus::ArtifactIncomplete { findings, .. } => {
                    // Typed non-admission: no add_decl, no checked count, no
                    // cache authority (the fln-env model tests pin
                    // is_cacheable/may_enter_environment to false).
                    artifact_incomplete.extend(findings);
                    continue;
                }
                other => {
                    panic!("declaration-closure census must be conclusive over Prelude: {other:?}")
                }
            }
        }
        items.push(WorkItem {
            lead: info.name().clone(),
            kind: kind_str,
            members: n_members,
            env: env.clone(),
            decl,
            info,
        });
        for &m in &unit.members {
            env = env
                .add_decl(infos[m].clone())
                .expect("one-name law over Prelude");
        }
    }
    // Canonical finding order regardless of Kahn/cyclic discovery order: the
    // witness digest is a function of the finding SET.
    artifact_incomplete.sort_by(|a, b| a.declaration.cmp(&b.declaration));
    PreparedReplay {
        items,
        unchecked,
        nested_full,
        artifact_incomplete,
        final_env: env,
        decls_total: infos.len(),
        units_total,
        cyclic_leads,
    }
}

/// One unit's authoritative outcome, canonically rendered: class, diagnostic,
/// and exact resource facts. The concatenation of these lines IS the verdict
/// stream whose digest the thread matrix compares.
#[derive(Clone, PartialEq, Eq)]
struct UnitOutcome {
    lead: String,
    kind: &'static str,
    members: u64,
    outcome: String,
    message: String,
    steps_used: u64,
    max_depth: u32,
}

impl UnitOutcome {
    fn canonical_line(&self, index: usize) -> String {
        format!(
            "{index}\u{1f}{}\u{1f}{}\u{1f}{}\u{1f}{}\u{1f}{}\u{1f}{}\u{1f}{}",
            self.lead,
            self.kind,
            self.members,
            self.outcome,
            self.message,
            self.steps_used,
            self.max_depth
        )
    }
}

struct MatrixRun {
    threads: usize,
    outcomes: Vec<UnitOutcome>,
    stream_digest: String,
    accepted: u64,
    inconclusive: u64,
    rejected: BTreeMap<String, u64>,
    steps_total: u64,
    depth_max: u32,
    duration_us: u128,
}

/// Check every prepared unit across `threads` workers pulling from a shared
/// cursor (a genuinely nondeterministic schedule), then merge in canonical
/// unit order. The kernel is pure and each unit's inputs are fixed by
/// `prepare_replay`, so the merged stream must be independent of the
/// schedule; the caller asserts exactly that across the matrix.
fn check_matrix_run(prep: &PreparedReplay, threads: usize, budget: Budget) -> MatrixRun {
    let started = Instant::now();
    let n = prep.items.len();
    let slots: Vec<OnceLock<Outcome<Verdict>>> = (0..n).map(|_| OnceLock::new()).collect();
    let cursor = AtomicUsize::new(0);
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| {
                loop {
                    let i = cursor.fetch_add(1, Ordering::Relaxed);
                    if i >= n {
                        break;
                    }
                    let item = &prep.items[i];
                    let verdict = fln_kernel::check(&item.env, &item.decl, budget);
                    slots[i]
                        .set(verdict)
                        .expect("each unit is checked exactly once");
                }
            });
        }
    });
    let mut outcomes = Vec::with_capacity(n);
    let mut accepted = 0u64;
    let mut inconclusive = 0u64;
    let mut rejected: BTreeMap<String, u64> = BTreeMap::new();
    let mut steps_total = 0u64;
    let mut depth_max = 0u32;
    let mut stream = String::new();
    for (i, item) in prep.items.iter().enumerate() {
        let verdict = slots[i].get().expect("worker pool drained the cursor");
        match verdict {
            Outcome::Complete(Verdict::Accepted { .. }) => {
                accepted += item.members;
            }
            Outcome::Complete(Verdict::Rejected { class, .. }) => {
                *rejected.entry(format!("{class:?}")).or_default() += item.members;
            }
            Outcome::Inconclusive(_) => {
                inconclusive += item.members;
            }
            // Internal faults are deliberately absent from all authoritative
            // census buckets. `verdict_facts` preserves the fault in the unit
            // stream, and the totality assertion below makes the run fail.
            Outcome::InternalFault(_) => {}
        }
        let (outcome, class, message, steps_used, max_depth) = verdict_facts(verdict);
        let outcome = match class {
            Some(class) => format!("{outcome}:{class}"),
            None => outcome,
        };
        steps_total = steps_total.saturating_add(steps_used);
        depth_max = depth_max.max(max_depth);
        let outcome = UnitOutcome {
            lead: item.lead.to_display_string(),
            kind: item.kind,
            members: item.members,
            outcome,
            message,
            steps_used,
            max_depth,
        };
        stream.push_str(&outcome.canonical_line(i));
        stream.push('\n');
        outcomes.push(outcome);
    }
    MatrixRun {
        threads,
        outcomes,
        stream_digest: hash(Domain::Fixture, stream.as_bytes()).to_hex(),
        accepted,
        inconclusive,
        rejected,
        steps_total,
        depth_max,
        duration_us: started.elapsed().as_micros(),
    }
}

/// Shared identity for every NDJSON row this rig emits: run wiring comes from
/// the lane driver via FLN_KERNEL_E2E_*; standalone `cargo test` runs get the
/// same defaults the environment-collision rig uses.
struct EmitCtx {
    run_id: String,
    cwd: String,
    argv: String,
    stdout_artifact: String,
    stderr_artifact: String,
    cache_state: String,
    input_root: String,
    platform: String,
    started: Instant,
}

impl EmitCtx {
    fn new(fixture_bytes: &[u8], default_argv: &str) -> EmitCtx {
        let mut run_id = std::env::var("FLN_KERNEL_E2E_RUN_ID")
            .unwrap_or_else(|_| "unit".to_string())
            .chars()
            .filter(|ch| ch.is_ascii_alphanumeric() || matches!(ch, '-' | '_'))
            .collect::<String>();
        if run_id.is_empty() {
            run_id.push_str("unit");
        }
        let artifact_fallback =
            std::env::var("FLN_KERNEL_E2E_ARTIFACT").unwrap_or_else(|_| "stdout".to_string());
        EmitCtx {
            run_id,
            cwd: std::env::current_dir()
                .map(|path| path.to_string_lossy().into_owned())
                .unwrap_or_else(|_| "unknown".to_string()),
            argv: std::env::var("FLN_KERNEL_E2E_ARGV").unwrap_or_else(|_| default_argv.to_string()),
            stdout_artifact: std::env::var("FLN_KERNEL_E2E_STDOUT_ARTIFACT")
                .unwrap_or_else(|_| artifact_fallback.clone()),
            stderr_artifact: std::env::var("FLN_KERNEL_E2E_STDERR_ARTIFACT")
                .unwrap_or(artifact_fallback),
            cache_state: std::env::var("FLN_KERNEL_E2E_CACHE_STATE")
                .unwrap_or_else(|_| "uncontrolled".to_string()),
            input_root: format!(
                "fln-fixture:{}",
                hash(Domain::Fixture, fixture_bytes).to_hex()
            ),
            platform: format!("{}-{}", std::env::consts::OS, std::env::consts::ARCH),
            started: Instant::now(),
        }
    }

    /// The governance prefix shared verbatim by both row schemas.
    fn prefix(&self, schema: &str, claim_id: &str, invariant_id: &str, scenario: &str) -> String {
        format!(
            "\"schema\":{},\"version\":2,\"run_id\":{},\"bead\":\"franken_lean-ap6\",\
             \"claim_id\":{},\"claim_type\":\"bounded_model\",\"invariant_id\":{},\
             \"invariant_relation\":\"single-authority-admission\",\
             \"determinism_invariant\":\"FL-INV-01\",\"gate_id\":\"G1\",\
             \"gate_relation\":\"partial-component-evidence\",\
             \"parity_ledger_row\":\"init-prelude-admission-replay\",\
             \"data_grade\":\"verified\",\"epoch\":\"lean-v4.32.0\",\"mode\":\"sound\",\
             \"profile\":\"e2e\",\"platform\":{},\"seed\":\"module-order-kahn-v1\",\
             \"cache_state\":{},\"canonical_input_root\":{},\"scenario\":{},\
             \"cwd\":{},\"argv\":[{}],\"stdout_artifact\":{},\"stderr_artifact\":{}",
            json_string(schema),
            json_string(&self.run_id),
            json_string(claim_id),
            json_string(invariant_id),
            json_string(&self.platform),
            json_string(&self.cache_state),
            json_string(&self.input_root),
            json_string(scenario),
            json_string(&self.cwd),
            json_string(&self.argv),
            json_string(&self.stdout_artifact),
            json_string(&self.stderr_artifact),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn matrix_row(
        &self,
        prep: &PreparedReplay,
        run: &MatrixRun,
        budget: Budget,
        phase: &str,
        status: &str,
        first_divergence: Option<&str>,
        final_root: &str,
        final_state: &str,
        start_us: u128,
    ) {
        let rejected_total: u64 = run.rejected.values().sum();
        // FL-INV-07: an inconclusive outcome was attempted, but it was not
        // checked to a verdict and must not enter the checked census.
        let checked = run.accepted + rejected_total;
        let end_us = self.started.elapsed().as_micros();
        println!(
            "{{{},\"phase\":{},\"threads\":{},\"status\":{},\"budget_steps\":{},\
             \"budget_depth\":{},\"decls_total\":{},\"units_total\":{},\"units_checked\":{},\
             \"units_cyclic\":{},\"checked\":{},\"accepted\":{},\"rejected_total\":{},\
             \"inconclusive\":{},\"artifact_incomplete\":{},\
             \"artifact_incomplete_witness\":{},\
             \"nested_partial_blocks\":0,\"nested_full_blocks\":{},\"verdict_stream_digest\":{},\
             \"final_logical_root\":{},\"steps_used_total\":{},\"max_depth_seen\":{},\
             \"monotonic_start_us\":{},\"monotonic_end_us\":{},\"duration_us\":{},\
             \"timing_used_as_gate\":false,\"process_exit\":0,\"signal\":null,\
             \"first_divergence\":{},\"cleanup_status\":\"retained_by_policy\",\
             \"final_state\":{}}}",
            self.prefix(
                "fln.e2e.kernel-admission",
                "franken_lean-ap6-admission-determinism",
                "FL-INV-02",
                "init-prelude-admission-thread-matrix",
            ),
            json_string(phase),
            run.threads,
            json_string(status),
            budget.steps,
            budget.depth,
            prep.decls_total,
            prep.units_total,
            prep.items.len(),
            prep.cyclic_leads.len(),
            checked,
            run.accepted,
            rejected_total,
            run.inconclusive,
            prep.artifact_incomplete_count(),
            json_string(&prep.artifact_witness_hex()),
            prep.nested_full,
            json_string(&run.stream_digest),
            json_string(final_root),
            run.steps_total,
            run.depth_max,
            start_us,
            end_us,
            run.duration_us,
            first_divergence.map_or("null".to_string(), json_string),
            json_string(final_state),
        );
    }

    /// One typed artifact-incomplete census row (bead
    /// franken_lean-artifact-incomplete-private-refs-sgt): the declaration,
    /// its safety class, its exact missing references, the finding-set
    /// witness, and the authority facts — never checked, never cacheable,
    /// never environment-admissible (FL-INV-07: an inconclusive-family
    /// outcome, not a verdict).
    fn artifact_incomplete_row(&self, finding: &MissingConstantFinding, witness_hex: &str) {
        let missing: Vec<String> = finding
            .missing
            .iter()
            .map(|name| json_string(&name.to_display_string()))
            .collect();
        println!(
            "{{{},\"phase\":\"artifact-incomplete-row\",\"declaration\":{},\"safety\":{},\
             \"missing_references\":[{}],\"witness\":{},\
             \"outcome\":\"inconclusive-artifact-incomplete\",\"authority\":\"none\",\
             \"kernel_checked\":false,\"cacheable\":false,\
             \"environment_admissible\":false,\"evidence_grade\":\"verified\"}}",
            self.prefix(
                "fln.e2e.kernel-admission",
                "franken_lean-sgt-artifact-completeness",
                "FL-INV-07",
                "init-prelude-artifact-incomplete-census",
            ),
            json_string(&finding.declaration.to_display_string()),
            json_string(match finding.safety {
                DefinitionSafety::Safe => "safe",
                DefinitionSafety::Unsafe => "unsafe",
                DefinitionSafety::Partial => "partial",
            }),
            missing.join(","),
            json_string(witness_hex),
        );
    }

    #[allow(clippy::too_many_arguments)]
    fn fault_row(
        &self,
        phase: &str,
        mutant_id: Option<&str>,
        target: &str,
        expected_outcome: &str,
        actual_outcome: &str,
        reject_class: Option<&str>,
        message_excerpt: &str,
        budget: Budget,
        steps_used: u64,
        max_depth: u32,
        root_before: &str,
        root_after: &str,
        atomicity_held: bool,
        recovery_outcome: Option<&str>,
        status: &str,
        final_state: &str,
        start_us: u128,
    ) {
        let end_us = self.started.elapsed().as_micros();
        let excerpt: String = message_excerpt.chars().take(160).collect();
        println!(
            "{{{},\"phase\":{},\"status\":{},\"mutant_id\":{},\"target\":{},\
             \"expected_outcome\":{},\
             \"actual_outcome\":{},\"reject_class\":{},\"message_excerpt\":{},\
             \"budget_steps\":{},\"budget_depth\":{},\"steps_used\":{},\"max_depth\":{},\
             \"root_before\":{},\"root_after\":{},\"atomicity_held\":{},\
             \"recovery_outcome\":{},\"monotonic_start_us\":{},\"monotonic_end_us\":{},\
             \"duration_us\":{},\"timing_used_as_gate\":false,\"process_exit\":0,\
             \"signal\":null,\"first_divergence\":null,\
             \"cleanup_status\":\"retained_by_policy\",\"final_state\":{}}}",
            self.prefix(
                "fln.e2e.kernel-admission-fault",
                "franken_lean-ap6-admission-fault-matrix",
                if phase.starts_with("resource") || phase.contains("recovery") {
                    "FL-INV-07"
                } else {
                    "FL-INV-02"
                },
                "kernel-admission-fault-matrix",
            ),
            json_string(phase),
            json_string(status),
            mutant_id.map_or("null".to_string(), json_string),
            json_string(target),
            json_string(expected_outcome),
            json_string(actual_outcome),
            reject_class.map_or("null".to_string(), json_string),
            json_string(&excerpt),
            budget.steps,
            budget.depth,
            steps_used,
            max_depth,
            json_string(root_before),
            json_string(root_after),
            atomicity_held,
            recovery_outcome.map_or("null".to_string(), json_string),
            start_us,
            end_us,
            end_us.saturating_sub(start_us),
            json_string(final_state),
        );
    }
}

fn decode_prelude() -> Option<(Vec<u8>, Vec<ConstantInfo>)> {
    let lib = reference_lib()?;
    let bytes = std::fs::read(lib.join("Init/Prelude.olean")).expect("read Init/Prelude.olean");
    let view = OleanView::parse(&bytes).expect("parse olean");
    let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
    let infos = decoder
        .decode_module_constants()
        .expect("decode Prelude constants");
    Some((bytes, infos))
}

#[test]
fn prelude_replays_through_the_kernel() {
    let Some((bytes, infos)) = decode_prelude() else {
        eprintln!(
            "SKIP kernel_replay: pinned Reference stdlib not found \
             (set FLN_REFERENCE_LIB or install the pin); typed limitation, not a pass"
        );
        return;
    };
    assert_eq!(infos.len(), 2204, "Prelude constant census at the pin");

    let module_by_name: HashMap<Name, ConstantInfo> = infos
        .iter()
        .map(|info| (info.name().clone(), info.clone()))
        .collect();

    // Probe lane (bead franken_lean-ap6): FLN_REPLAY_ADMISSION_CENSUS=1
    // classifies the block/quotient/non-safe-definition feature surface —
    // which KR-6xx/7xx/8xx/95x/97x machinery this corpus exercises, measured
    // from decoded declarations rather than guessed from the pin.
    if std::env::var("FLN_REPLAY_ADMISSION_CENSUS").is_ok() {
        let mut block_sizes: BTreeMap<usize, u64> = BTreeMap::new();
        let mut ctor_counts: BTreeMap<usize, u64> = BTreeMap::new();
        let mut lparam_counts: BTreeMap<usize, u64> = BTreeMap::new();
        let mut with_indices = 0u64;
        let mut nested: Vec<String> = Vec::new();
        let mut reflexive: Vec<String> = Vec::new();
        let mut unsafe_inds: Vec<String> = Vec::new();
        let mut recursive = 0u64;
        let mut rec_k: Vec<String> = Vec::new();
        let mut rec_multi_motive: Vec<String> = Vec::new();
        let mut rec_lparams_extra = 0u64;
        let mut rec_lparams_same = 0u64;
        let mut max_fields = 0u32;
        let mut def_safety: BTreeMap<String, u64> = BTreeMap::new();
        let mut def_names: Vec<String> = Vec::new();
        let mut quots: Vec<String> = Vec::new();
        for (i, _) in infos.iter().enumerate() {
            match &infos[i] {
                ConstantInfo::Induct(ind) => {
                    *block_sizes.entry(ind.all.len()).or_default() += 1;
                    *ctor_counts.entry(ind.ctors.len()).or_default() += 1;
                    *lparam_counts
                        .entry(ind.base.level_params.len())
                        .or_default() += 1;
                    if ind.num_indices > 0 {
                        with_indices += 1;
                    }
                    if ind.num_nested > 0 {
                        nested.push(ind.base.name.to_display_string());
                    }
                    if ind.is_reflexive {
                        reflexive.push(ind.base.name.to_display_string());
                    }
                    if ind.is_unsafe {
                        unsafe_inds.push(ind.base.name.to_display_string());
                    }
                    if ind.is_rec {
                        recursive += 1;
                    }
                }
                ConstantInfo::Ctor(ctor) => {
                    max_fields = max_fields.max(ctor.num_fields);
                }
                ConstantInfo::Rec(rec) => {
                    if rec.k {
                        rec_k.push(rec.base.name.to_display_string());
                    }
                    if rec.num_motives > 1 {
                        rec_multi_motive.push(rec.base.name.to_display_string());
                    }
                    let ind_lparams = module_by_name
                        .get(&rec.base.name.parent())
                        .map(|info| info.constant_val().level_params.len());
                    match ind_lparams {
                        Some(n) if rec.base.level_params.len() == n + 1 => rec_lparams_extra += 1,
                        Some(n) if rec.base.level_params.len() == n => rec_lparams_same += 1,
                        _ => {}
                    }
                }
                ConstantInfo::Quot(q) => {
                    quots.push(format!(
                        "{}:{:?}",
                        infos[i].name().to_display_string(),
                        q.kind
                    ));
                }
                ConstantInfo::Defn(d) if d.safety != DefinitionSafety::Safe => {
                    *def_safety.entry(format!("{:?}", d.safety)).or_default() += 1;
                    if def_names.len() < 40 {
                        def_names.push(infos[i].name().to_display_string());
                    }
                }
                _ => {}
            }
        }
        eprintln!("ADMISSION CENSUS (block/quot/non-safe-def features, bead franken_lean-ap6):");
        eprintln!("  inductive blocks: sizes(all.len->n)={block_sizes:?} ctors={ctor_counts:?}");
        eprintln!(
            "  inductive lparams={lparam_counts:?} with_indices={with_indices} recursive={recursive}"
        );
        eprintln!(
            "  nested({})={:?}",
            nested.len(),
            &nested[..nested.len().min(12)]
        );
        eprintln!(
            "  reflexive({})={:?}",
            reflexive.len(),
            &reflexive[..reflexive.len().min(12)]
        );
        eprintln!("  unsafe({})={:?}", unsafe_inds.len(), unsafe_inds);
        eprintln!(
            "  recursors: K({})={:?} multi-motive({})={:?} lparams(extra-elim/same)={}/{}",
            rec_k.len(),
            &rec_k[..rec_k.len().min(12)],
            rec_multi_motive.len(),
            rec_multi_motive,
            rec_lparams_extra,
            rec_lparams_same
        );
        eprintln!("  ctor max_fields={max_fields}");
        eprintln!("  non-safe defs by safety={def_safety:?} names={def_names:?}");
        eprintln!("  quots={quots:?}");
        // Nested-block deep probe (bead franken_lean-8ce): the exact decoded
        // shapes the _nested.* auxiliary translation must reconstruct — the
        // nested block's ctor field types (where `Array Syntax`-class
        // occurrences live), its multi-motive recursor telescope and rule
        // RHSes, and the environment specs of the nested heads the pin would
        // copy (their own params/ctors, instantiated during translation).
        for (i, _) in infos.iter().enumerate() {
            let ConstantInfo::Induct(ind) = &infos[i] else {
                continue;
            };
            if ind.num_nested == 0 {
                continue;
            }
            eprintln!(
                "  NESTED BLOCK {}: num_nested={} num_params={} num_indices={} lparams={:?}",
                ind.base.name.to_display_string(),
                ind.num_nested,
                ind.num_params,
                ind.num_indices,
                ind.base.level_params
            );
            eprintln!("    type = {}", shape(&ind.base.type_, 8));
            let mut nested_heads: HashSet<Name> = HashSet::new();
            for ctor_name in &ind.ctors {
                let Some(ConstantInfo::Ctor(c)) = module_by_name.get(ctor_name) else {
                    continue;
                };
                eprintln!(
                    "    ctor {} (fields={}) = {}",
                    c.base.name.to_display_string(),
                    c.num_fields,
                    shape(&c.base.type_, 10)
                );
                let mut refs = HashSet::new();
                const_refs(&c.base.type_, &mut refs);
                for r in refs {
                    if r != ind.base.name {
                        nested_heads.insert(r);
                    }
                }
            }
            for (j, info_j) in infos.iter().enumerate() {
                let ConstantInfo::Rec(r) = info_j else {
                    continue;
                };
                if r.all.first() != Some(&ind.base.name) {
                    continue;
                }
                let _ = j;
                eprintln!(
                    "    recursor {} motives={} minors={} params={} indices={} k={} lparams={:?}",
                    r.base.name.to_display_string(),
                    r.num_motives,
                    r.num_minors,
                    r.num_params,
                    r.num_indices,
                    r.k,
                    r.base.level_params
                );
                eprintln!("      type = {}", shape(&r.base.type_, 12));
                for rule in &r.rules {
                    eprintln!(
                        "      rule {} nfields={} rhs={}",
                        rule.ctor.to_display_string(),
                        rule.nfields,
                        shape(&rule.rhs, 10)
                    );
                }
            }
            let mut heads: Vec<String> = nested_heads.iter().map(Name::to_display_string).collect();
            heads.sort();
            eprintln!("    ctor-referenced heads = {heads:?}");
            for head in &nested_heads {
                if let Some(ConstantInfo::Induct(h)) = module_by_name.get(head) {
                    eprintln!(
                        "    head spec {}: params={} indices={} all={:?} ctors={:?} lparams={:?} type={}",
                        h.base.name.to_display_string(),
                        h.num_params,
                        h.num_indices,
                        h.all
                            .iter()
                            .map(Name::to_display_string)
                            .collect::<Vec<_>>(),
                        h.ctors
                            .iter()
                            .map(Name::to_display_string)
                            .collect::<Vec<_>>(),
                        h.base.level_params,
                        shape(&h.base.type_, 6)
                    );
                    for cn in &h.ctors {
                        if let Some(ConstantInfo::Ctor(hc)) = module_by_name.get(cn) {
                            eprintln!(
                                "      head ctor {} (fields={}) = {}",
                                hc.base.name.to_display_string(),
                                hc.num_fields,
                                shape(&hc.base.type_, 10)
                            );
                        }
                    }
                }
            }
        }
    }

    let prep = prepare_replay(&infos);
    for lead in prep.cyclic_leads.iter().take(10) {
        eprintln!("  cyclic unit: [{lead:?}]");
    }
    let emit = EmitCtx::new(
        &bytes,
        "cargo test -q -p fln-conformance --test kernel_replay \
         prelude_replays_through_the_kernel -- --exact --nocapture",
    );
    let final_root = prep.final_env.logical_root(&KVMap::new()).to_string();
    let budget = Budget::DEFAULT;

    // The deterministic thread matrix (the ap6 acceptance contract): the same
    // prepared units checked at {1, 8, 32} workers over a shared racing
    // cursor. The merged authoritative stream — verdicts, diagnostics, exact
    // consumption — must be byte-identical at every width.
    let mut runs: Vec<MatrixRun> = Vec::new();
    for threads in [1usize, 8, 32] {
        let start_us = emit.started.elapsed().as_micros();
        let run = check_matrix_run(&prep, threads, budget);
        eprintln!(
            "kernel_replay matrix: threads={} accepted={} rejected_total={} \
             inconclusive={} steps_total={} depth_max={} digest={} ({} us)",
            run.threads,
            run.accepted,
            run.rejected.values().sum::<u64>(),
            run.inconclusive,
            run.steps_total,
            run.depth_max,
            run.stream_digest,
            run.duration_us,
        );
        emit.matrix_row(
            &prep,
            &run,
            budget,
            &format!("matrix-threads-{threads}"),
            "pass",
            None,
            &final_root,
            "verdict-stream-merged-canonical-order",
            start_us,
        );
        runs.push(run);
    }

    // Byte-identity across the matrix: find the first divergence (if any),
    // emit the identity row carrying it, and only then assert — so a failure
    // leaves machine evidence behind, not just a panic message.
    let baseline = &runs[0];
    let mut first_divergence: Option<String> = None;
    'outer: for run in &runs[1..] {
        if run.stream_digest == baseline.stream_digest {
            continue;
        }
        for (i, (a, b)) in baseline
            .outcomes
            .iter()
            .zip(run.outcomes.iter())
            .enumerate()
        {
            if a != b {
                first_divergence = Some(format!(
                    "threads={} unit={} lead={}: {} vs {}",
                    run.threads, i, a.lead, a.outcome, b.outcome
                ));
                break 'outer;
            }
        }
        first_divergence = Some(format!(
            "threads={}: digest mismatch with equal prefixes",
            run.threads
        ));
        break;
    }
    let identical = first_divergence.is_none()
        && runs
            .iter()
            .all(|r| r.steps_total == baseline.steps_total && r.depth_max == baseline.depth_max);
    let start_us = emit.started.elapsed().as_micros();
    emit.matrix_row(
        &prep,
        baseline,
        budget,
        "matrix-identity",
        if identical { "pass" } else { "fail" },
        first_divergence.as_deref(),
        &final_root,
        if identical {
            "byte-identical-across-1-8-32"
        } else {
            "MATRIX-DIVERGENCE"
        },
        start_us,
    );
    assert!(
        identical,
        "FL-INV-01 violation: verdict stream diverged across the thread matrix: \
         {first_divergence:?}"
    );

    // Census + triage over the (identical) baseline run.
    let accepted = baseline.accepted;
    let inconclusive = baseline.inconclusive;
    let rejected = &baseline.rejected;
    let mut gap_families: BTreeMap<&'static str, u64> = BTreeMap::new();
    let mut reasons: BTreeMap<String, u64> = BTreeMap::new();
    let mut rejected_names: Vec<String> = Vec::new();
    for (i, outcome) in baseline.outcomes.iter().enumerate() {
        if !outcome.outcome.starts_with("rejected:") {
            continue;
        }
        let item = &prep.items[i];
        *gap_families
            .entry(reduction_gap_family(&item.lead))
            .or_default() += outcome.members;
        *reasons
            .entry(format!("{}: {}", outcome.outcome, outcome.message))
            .or_default() += 1;
        if rejected_names.len() < 20 {
            rejected_names.push(format!("{} ({})", outcome.lead, outcome.outcome));
        }
        // Probe lane (bead fln-d4x): FLN_REPLAY_PROBE is a comma list of
        // declaration names; matching rejections dump bounded type and value
        // shapes so a reduction-gap hypothesis can be anchored in the DECODED
        // term, not guessed from the name.
        if let Ok(probe) = std::env::var("FLN_REPLAY_PROBE") {
            let name = outcome.lead.clone();
            if probe.split(',').any(|entry| entry.trim() == name) {
                eprintln!("PROBE {name} [{}: {}]", outcome.outcome, outcome.message);
                eprintln!("  type  = {}", shape(&item.info.constant_val().type_, 6));
                if let ConstantInfo::Defn(defn) = &item.info {
                    eprintln!("  value = {}", shape(&defn.value, 8));
                }
                // Companion env dump: what does the CHECKING environment
                // actually hold for these names at this rejection?
                if let Ok(names) = std::env::var("FLN_REPLAY_PROBE_ENV") {
                    for entry in names.split(',') {
                        let mut target = Name::anonymous();
                        for seg in entry.trim().split('.') {
                            target = Name::str(target, seg);
                        }
                        match item.env.find(&target) {
                            Some(ConstantInfo::Defn(d)) => eprintln!(
                                "  env {} = definition safety={:?} hints={:?} value={}",
                                entry.trim(),
                                d.safety,
                                d.hints,
                                shape(&d.value, 4)
                            ),
                            Some(other) => {
                                eprintln!("  env {} = {}", entry.trim(), other.kind_name())
                            }
                            None => eprintln!("  env {} = ABSENT", entry.trim()),
                        }
                    }
                }
            }
        }
    }

    // FL-INV-07: only complete Accepted/Rejected verdicts are checked.
    // Any inconclusive outcome remains separately visible and makes the
    // conservation assertion below fail instead of being laundered into this
    // count.
    let checked = accepted + rejected.values().sum::<u64>();
    let unchecked = &prep.unchecked;
    let artifact_incomplete = prep.artifact_incomplete_count();
    let artifact_witness = prep.artifact_witness_hex();
    eprintln!(
        "kernel_replay census: checked={checked} accepted={accepted} \
         inconclusive={inconclusive} rejected={rejected:?} unchecked={unchecked:?} \
         artifact_incomplete={artifact_incomplete} \
         artifact_incomplete_witness={artifact_witness} \
         nested_partial_blocks=0 nested_full_blocks={}",
        prep.nested_full
    );
    // One typed row per artifact-incomplete declaration, bound by the witness.
    for finding in &prep.artifact_incomplete {
        emit.artifact_incomplete_row(finding, &artifact_witness);
    }
    if !rejected_names.is_empty() {
        eprintln!("first rejections: {rejected_names:?}");
        let mut by_count: Vec<_> = reasons.iter().collect();
        by_count.sort_by(|a, b| b.1.cmp(a.1));
        for (reason, n) in by_count.iter().take(12) {
            eprintln!("  {n:>5}  {reason}");
        }
    }

    eprintln!("kernel_replay triage (reduction-gap families): {gap_families:?}");

    // Census law: every declaration lands in exactly one typed bucket —
    // validated (checked through the sole kernel authority), unsafe-not-
    // kernel-checked (kinds with no admission rule yet; Init.Prelude has
    // none), or artifact-incomplete — and the three families are never
    // folded into one another (bead franken_lean-artifact-incomplete-
    // private-refs-sgt: no typed limitation may disappear into a success
    // total).
    let unchecked_total: u64 = unchecked.values().sum();
    assert_eq!(checked + unchecked_total + artifact_incomplete, 2204);
    assert_eq!(
        unchecked_total, 0,
        "a declaration kind bypassed the kernel: {unchecked:?}"
    );
    // The exact six artifact-incomplete rows at the pin: each non-safe
    // implementation helper with its exact missing private auxiliaries. A
    // name-only exception cannot satisfy this pin — the census computes the
    // rows from decoded dependencies, and this assertion binds declaration,
    // safety class, and missing-reference set alike.
    let expected_rows: [(&str, &str, &[&str]); 6] = [
        (
            "Lean.Name.hash._override",
            "unsafe",
            &["_private.Init.Prelude.0.Lean.Name.hash._proof_1"],
        ),
        (
            "Lean.Name.num._override",
            "unsafe",
            &["_private.Init.Prelude.0.Lean.Name.hash._proof_2"],
        ),
        (
            "Lean.Syntax.getHeadInfo?._unsafe_rec",
            "partial",
            &["_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1"],
        ),
        (
            "Lean.Syntax.getTailPos?._unsafe_rec",
            "partial",
            &["_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1"],
        ),
        (
            "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
            "partial",
            &["_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1"],
        ),
        (
            "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
            "partial",
            &["_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop.match_1"],
        ),
    ];
    let actual_rows: Vec<(String, &'static str, Vec<String>)> = prep
        .artifact_incomplete
        .iter()
        .map(|finding| {
            (
                finding.declaration.to_display_string(),
                match finding.safety {
                    DefinitionSafety::Safe => "safe",
                    DefinitionSafety::Unsafe => "unsafe",
                    DefinitionSafety::Partial => "partial",
                },
                finding
                    .missing
                    .iter()
                    .map(|name| name.to_display_string())
                    .collect::<Vec<_>>(),
            )
        })
        .collect();
    let expected_rows: Vec<(String, &str, Vec<String>)> = expected_rows
        .iter()
        .map(|(declaration, safety, missing)| {
            (
                declaration.to_string(),
                *safety,
                missing.iter().map(|m| m.to_string()).collect(),
            )
        })
        .collect();
    assert_eq!(
        actual_rows, expected_rows,
        "the artifact-incomplete census drifted from the pin"
    );
    // None of the six entered the environment (the ap6-era insertion was the
    // bug this bead governs) — and every complete declaration did.
    for finding in &prep.artifact_incomplete {
        assert!(
            prep.final_env.find(&finding.declaration).is_none(),
            "artifact-incomplete declaration `{}` entered the environment",
            finding.declaration.to_display_string()
        );
    }

    // Never Inconclusive: the default budget suffices for every Prelude
    // declaration K1 can check (FL-INV-07 — exhaustion would be honest, but
    // there is none at this scale).
    assert_eq!(inconclusive, 0, "unexpected budget exhaustion");

    // The kernel genuinely accepts a large body of real Reference statements
    // and proofs — a regression that rejected everything cannot hide here.
    // 1233/1755 is the fragment checkable without the missing reduction rules;
    // the floor guards against regression without pinning the exact count.
    assert!(
        accepted >= 1200,
        "accepted only {accepted}/{checked} checked declarations — K1 regressed"
    );

    // The spike's core soundness finding (acceptance criterion (b)): the
    // Reference kernel ACCEPTED every declaration in this module when it wrote
    // the olean. Therefore every FrankenLean rejection here is, by definition,
    // a false-REJECT — a completeness gap — and NEVER a false-accept. K1 admits
    // nothing the Reference refused (there is nothing it refused). Soundness in
    // the sense that matters (FL-INV-02: no bad constant admitted) holds
    // trivially on this corpus; what remains is exactly the reduction-rule
    // completeness work, triaged into named families above.
    //
    // Guard that the rejection CLASSES stay within the reduction/inference-gap
    // set. A new class here (e.g. a level or binder soundness class) would be a
    // genuinely new divergence and must be triaged before it lands.
    let known_gap_classes = [
        "TypeMismatch",
        "FunctionExpected",
        "InvalidProjection",
        "DefinitionTypeMismatch",
    ];
    for class in rejected.keys() {
        assert!(
            known_gap_classes.iter().any(|k| k == class),
            "rejection class {class} is not a pre-classified reduction gap — triage before landing"
        );
    }

    // And that the triage is total: every rejection landed in a named family.
    let rejected_total: u64 = rejected.values().sum();
    assert_eq!(
        gap_families.values().sum::<u64>(),
        rejected_total,
        "triage did not classify every rejection"
    );
}

// ---------------------------------------------------------------------------
// The admission fault matrix (bead franken_lean-ap6 acceptance): named
// single-defect data-mutants on REAL decoded Reference declarations, exact
// budget boundaries, typed exhaustion, failure atomicity, and recovery —
// every phase through the one public authority, every phase leaving an
// NDJSON row behind.
// ---------------------------------------------------------------------------

fn item_by_lead<'a>(prep: &'a PreparedReplay, lead: &str) -> &'a WorkItem {
    prep.items
        .iter()
        .find(|item| item.lead.to_display_string() == lead)
        .unwrap_or_else(|| panic!("Init.Prelude unit `{lead}` not found"))
}

/// The quotient-initialization unit, found structurally (its lead is whichever
/// `Quot` declaration the pin serialized first — a name we must not guess).
fn quot_item(prep: &PreparedReplay) -> &WorkItem {
    prep.items
        .iter()
        .find(|item| item.kind == "quot")
        .expect("Init.Prelude has the quotient-initialization unit")
}

fn structural_unit_evidence_name(unit: StructuralUnit) -> &'static str {
    match unit {
        StructuralUnit::InputBytes => "InputBytes",
        StructuralUnit::ProducedNodes => "ProducedNodes",
        StructuralUnit::ExpandedWeight => "ExpandedWeight",
    }
}

fn resource_usage_facts(usage: &ResourceUsage) -> (String, u64, u32) {
    match usage.reason {
        ResourceReason::Heartbeats { .. } => ("inconclusive:Steps".into(), usage.observed, 0),
        ResourceReason::RecursionDepth { .. } => (
            "inconclusive:Depth".into(),
            0,
            u32::try_from(usage.observed).unwrap_or(u32::MAX),
        ),
        ResourceReason::Cancelled => ("inconclusive:Cancelled".into(), 0, 0),
        ResourceReason::Memory { .. } => ("inconclusive:Memory".into(), usage.observed, 0),
        ResourceReason::StructuralBudget { unit } => (
            format!(
                "inconclusive:StructuralBudget:{}",
                structural_unit_evidence_name(unit)
            ),
            // Structural allowances are neither kernel steps nor recursion
            // depth. Their allowed/observed values remain typed on
            // ResourceUsage instead of being mislabeled in these fields.
            0,
            0,
        ),
    }
}

fn assert_structural_budget_resource_facts_are_total() {
    let expected = [
        (
            StructuralUnit::InputBytes,
            "inconclusive:StructuralBudget:InputBytes",
        ),
        (
            StructuralUnit::ProducedNodes,
            "inconclusive:StructuralBudget:ProducedNodes",
        ),
        (
            StructuralUnit::ExpandedWeight,
            "inconclusive:StructuralBudget:ExpandedWeight",
        ),
    ];
    assert_eq!(
        expected.len(),
        StructuralUnit::ALL.len(),
        "every structural-budget unit needs an explicit evidence classification"
    );
    for ((unit, expected_outcome), registered_unit) in expected.into_iter().zip(StructuralUnit::ALL)
    {
        assert_eq!(
            unit, registered_unit,
            "structural-budget evidence order drifted from the D8 taxonomy"
        );
        let usage = ResourceUsage {
            reason: ResourceReason::StructuralBudget { unit },
            allowed: 64,
            observed: 65,
        };
        assert!(usage.is_genuine_exhaustion());
        assert_eq!(
            resource_usage_facts(&usage),
            (expected_outcome.to_string(), 0, 0)
        );
        assert_eq!(
            (usage.allowed, usage.observed),
            (64, 65),
            "structural allowed/observed facts changed meaning"
        );
    }
}

fn resource_exhaustion(v: &Outcome<Verdict>) -> Option<&ResourceUsage> {
    match v {
        Outcome::Inconclusive(inconclusive) => match &inconclusive.cause {
            InconclusiveCause::ResourceExhausted { usage } => Some(usage),
            InconclusiveCause::Cancelled { .. }
            | InconclusiveCause::DependencyUnavailable { .. }
            | InconclusiveCause::AuthorityIncomplete { .. } => None,
        },
        Outcome::Complete(_) | Outcome::InternalFault(_) => None,
    }
}

fn verdict_facts(v: &Outcome<Verdict>) -> (String, Option<String>, String, u64, u32) {
    match v {
        Outcome::Complete(Verdict::Accepted { consumption }) => (
            "accepted".into(),
            None,
            String::new(),
            consumption.steps_used,
            consumption.max_depth,
        ),
        Outcome::Complete(Verdict::Rejected {
            class,
            message,
            consumption,
        }) => (
            "rejected".into(),
            Some(format!("{class:?}")),
            message.clone(),
            consumption.steps_used,
            consumption.max_depth,
        ),
        Outcome::Inconclusive(inconclusive) => match &inconclusive.cause {
            InconclusiveCause::ResourceExhausted { usage } => {
                let (outcome, steps_used, max_depth) = resource_usage_facts(usage);
                (outcome, None, String::new(), steps_used, max_depth)
            }
            InconclusiveCause::Cancelled { at } => (
                "inconclusive:Cancelled".into(),
                None,
                at.text().to_string(),
                0,
                0,
            ),
            InconclusiveCause::DependencyUnavailable { what } => (
                "inconclusive:DependencyUnavailable".into(),
                None,
                what.text().to_string(),
                0,
                0,
            ),
            InconclusiveCause::AuthorityIncomplete { what } => (
                "inconclusive:AuthorityIncomplete".into(),
                None,
                what.text().to_string(),
                0,
                0,
            ),
        },
        Outcome::InternalFault(fault) => (
            "internal_fault".into(),
            None,
            format!("{}: {}", fault.invariant, fault.detail.text()),
            0,
            0,
        ),
    }
}

#[test]
fn admission_fault_matrix_is_typed_and_atomic() {
    // This taxonomy-totality proof runs even when the pinned Reference is
    // absent and the real-module portion below must skip.
    assert_structural_budget_resource_facts_are_total();

    let Some((bytes, infos)) = decode_prelude() else {
        eprintln!(
            "SKIP admission_fault_matrix: pinned Reference stdlib not found \
             (set FLN_REFERENCE_LIB or install the pin); typed limitation, not a pass"
        );
        return;
    };
    let prep = prepare_replay(&infos);
    let emit = EmitCtx::new(
        &bytes,
        "cargo test -q -p fln-conformance --test kernel_replay \
         admission_fault_matrix_is_typed_and_atomic -- --exact --nocapture",
    );
    let options = KVMap::new();
    let budget = Budget::DEFAULT;

    // --- named single-defect data-mutants on real declarations ------------
    // Each mutant perturbs ONE decoded observable; the kernel must reject it
    // with the expected class, the environment must be untouched (root
    // identity), and the pristine unit must still be accepted afterwards
    // (recovery). Never a panic, never a silent accept, never Inconclusive.
    struct MutantCase {
        id: &'static str,
        target: String,
        expected_class: &'static str,
        message_must_contain: &'static str,
        decl: Declaration,
        env_lead: String,
    }

    let mut cases: Vec<MutantCase> = Vec::new();

    // 1. trusted-decoded-recursor-rules: swap the two Bool.rec rule RHSes.
    //    KR-800..803 regenerate the recursor and compare byte-exact — a
    //    kernel that TRUSTED the decoded rows would admit this corruption.
    {
        let item = item_by_lead(&prep, "Bool");
        let Declaration::Inductive(block) = &item.decl else {
            panic!("Bool unit is a block");
        };
        let mut block = block.clone();
        assert_eq!(block.recursors.len(), 1, "Bool has one recursor");
        assert_eq!(block.recursors[0].rules.len(), 2, "Bool.rec has two rules");
        let rhs0 = block.recursors[0].rules[0].rhs.clone();
        block.recursors[0].rules[0].rhs = block.recursors[0].rules[1].rhs.clone();
        block.recursors[0].rules[1].rhs = rhs0;
        cases.push(MutantCase {
            id: "tampered_recursor_rhs",
            target: "Bool.rec".to_string(),
            expected_class: "BlockMismatch",
            message_must_contain: "",
            decl: Declaration::Inductive(block),
            env_lead: "Bool".to_string(),
        });
    }

    // 2. dropped-positivity witness: rewrite `Nat.succ : Nat → Nat` into
    //    `succ : (Nat → Nat) → Nat` — a textbook non-positive occurrence.
    //    KR-606 must fire; a kernel with positivity skipped admits it.
    {
        let item = item_by_lead(&prep, "Nat");
        let Declaration::Inductive(block) = &item.decl else {
            panic!("Nat unit is a block");
        };
        let mut block = block.clone();
        let nat = block.types[0].base.name.clone();
        let succ = block
            .ctors
            .iter_mut()
            .find(|c| c.base.name.to_display_string() == "Nat.succ")
            .expect("Nat.succ present");
        let nat_e = || Expr::const_(nat.clone(), vec![]);
        succ.base.type_ = Expr::forall_e(
            Name::str(Name::anonymous(), "n"),
            Expr::forall_e(
                Name::str(Name::anonymous(), "x"),
                nat_e(),
                nat_e(),
                BinderInfo::Default,
            ),
            nat_e(),
            BinderInfo::Default,
        );
        // The tampered field also makes `Nat` reflexive; align the decoded
        // flag so the observable cross-check passes and the SINGLE defect
        // this mutant witnesses is the positivity law itself (KR-606).
        block.types[0].is_reflexive = true;
        cases.push(MutantCase {
            id: "nonpositive_ctor_field",
            target: "Nat.succ".to_string(),
            expected_class: "BlockMismatch",
            message_must_contain: "non positive occurrence",
            decl: Declaration::Inductive(block),
            env_lead: "Nat".to_string(),
        });
    }

    // 3. inverted-universe witness: give `Nat.succ` a field living in a
    //    universe strictly above `Nat`'s. The KR-604 field-universe law must
    //    reject; an inverted comparison admits it.
    {
        let item = item_by_lead(&prep, "Nat");
        let Declaration::Inductive(block) = &item.decl else {
            panic!("Nat unit is a block");
        };
        let mut block = block.clone();
        let nat = block.types[0].base.name.clone();
        let succ = block
            .ctors
            .iter_mut()
            .find(|c| c.base.name.to_display_string() == "Nat.succ")
            .expect("Nat.succ present");
        let type_2 = fln_core::level::Level::zero()
            .succ()
            .expect("shallow level")
            .succ()
            .expect("shallow level");
        succ.base.type_ = Expr::forall_e(
            Name::str(Name::anonymous(), "n"),
            Expr::sort(type_2),
            Expr::const_(nat, vec![]),
            BinderInfo::Default,
        );
        // Replacing the recursive field removes `Nat`'s self-occurrence;
        // align the decoded recursivity flag so the SINGLE defect this
        // mutant witnesses is the field-universe law itself (KR-604).
        block.types[0].is_rec = false;
        cases.push(MutantCase {
            id: "inverted_universe_ctor_field",
            target: "Nat.succ".to_string(),
            expected_class: "BlockMismatch",
            message_must_contain: "too big",
            decl: Declaration::Inductive(block),
            env_lead: "Nat".to_string(),
        });
    }

    // 4. skipped-quotient-sequencing witness: drop `Quot.ind` from the
    //    4-declaration initialization. KR-95x demands the exact well-formed
    //    init sequence; a kernel that skipped the sequence check admits it.
    {
        let item = quot_item(&prep);
        let Declaration::Quotient(decls) = &item.decl else {
            panic!("Quot unit is the quotient init");
        };
        let mut decls = decls.clone();
        assert_eq!(decls.len(), 4, "quotient init is 4 declarations");
        decls.pop();
        cases.push(MutantCase {
            id: "quotient_missing_member",
            target: "Quot.ind".to_string(),
            expected_class: "BlockMismatch",
            message_must_contain: "quotient initialization needs 4 declarations",
            decl: Declaration::Quotient(decls),
            env_lead: item.lead.to_display_string(),
        });
    }

    // 5. definition-type-swap witness: declare a real safe definition at
    //    another definition's (different) statement. The declared type and
    //    the value's inferred type cannot be defeq; admission must reject.
    //    (Init.Prelude serializes no `Thm` constants — definitions carry the
    //    declared-type-versus-value law here.)
    {
        let mut defns = prep.items.iter().filter_map(|item| {
            if let ConstantInfo::Defn(v) = &item.info
                && v.safety == DefinitionSafety::Safe
            {
                Some((item, v.clone()))
            } else {
                None
            }
        });
        let (_, defn_a) = defns.next().expect("a first safe definition");
        let (item_b, defn_b) = defns
            .find(|(_, b)| b.base.type_ != defn_a.base.type_)
            .expect("a second safe definition with a different type");
        // The LATER definition takes the EARLIER one's statement, so every
        // constant in the swapped type is already in the checking
        // environment and the rejection witnesses the declared-type-versus-
        // value law itself, not name resolution.
        let mut swapped = defn_b.clone();
        swapped.base.type_ = defn_a.base.type_.clone();
        cases.push(MutantCase {
            id: "definition_type_swap",
            target: item_b.lead.to_display_string(),
            expected_class: "",
            message_must_contain: "",
            decl: Declaration::Defn(swapped),
            env_lead: item_b.lead.to_display_string(),
        });
    }

    // 6. mutual-membership witness: a block whose leader CLAIMS a second
    //    mutual member that the block does not contain (KR-97x observable
    //    cross-checks; mutual-block membership is part of declaration
    //    content per fln-amv.1). A kernel that trusted the decoded `all`
    //    list without cross-checking admits it.
    {
        let item = item_by_lead(&prep, "Bool");
        let Declaration::Inductive(block) = &item.decl else {
            panic!("Bool unit is a block");
        };
        let mut block = block.clone();
        block.types[0]
            .all
            .push(Name::str(Name::anonymous(), "BoolPhantom"));
        cases.push(MutantCase {
            id: "mutual_membership_mismatch",
            target: "Bool".to_string(),
            expected_class: "BlockMismatch",
            message_must_contain: "",
            decl: Declaration::Inductive(block),
            env_lead: "Bool".to_string(),
        });
    }

    for case in &cases {
        let start_us = emit.started.elapsed().as_micros();
        let item = item_by_lead(&prep, &case.env_lead);
        let root_before = item.env.logical_root(&options).to_string();
        let verdict = fln_kernel::check(&item.env, &case.decl, budget);
        let (actual, class, message, steps_used, max_depth) = verdict_facts(&verdict);
        let root_after = item.env.logical_root(&options).to_string();
        let atomicity_held = root_before == root_after;
        // Recovery: the pristine unit still checks clean against the same env.
        let recovery = fln_kernel::check(&item.env, &item.decl, budget);
        let (recovery_outcome, _, _, _, _) = verdict_facts(&recovery);
        let class_ok =
            case.expected_class.is_empty() || class.as_deref() == Some(case.expected_class);
        let message_ok =
            case.message_must_contain.is_empty() || message.contains(case.message_must_contain);
        let killed = actual == "rejected" && class_ok && message_ok;
        let status = if killed && atomicity_held && recovery_outcome == "accepted" {
            "pass"
        } else {
            "fail"
        };
        eprintln!(
            "fault_matrix mutant {}: verdict={} class={:?} atomicity={} recovery={} — {}",
            case.id, actual, class, atomicity_held, recovery_outcome, status
        );
        emit.fault_row(
            &format!("mutant:{}", case.id),
            Some(case.id),
            &case.target,
            "rejected",
            &actual,
            class.as_deref(),
            &message,
            budget,
            steps_used,
            max_depth,
            &root_before,
            &root_after,
            atomicity_held,
            Some(&recovery_outcome),
            status,
            if killed {
                "mutant-killed-typed-rejection"
            } else {
                "MUTANT-SURVIVED"
            },
            start_us,
        );
        assert!(
            killed,
            "mutant {} was NOT killed: verdict={actual} class={class:?} message={message}",
            case.id
        );
        assert!(atomicity_held, "mutant {} mutated the environment", case.id);
        assert_eq!(
            recovery_outcome, "accepted",
            "recovery after mutant {} failed",
            case.id
        );
    }

    // --- typed resource exhaustion, exact boundaries, recovery ------------
    // FL-INV-07 end-to-end on a REAL declaration: exhaustion is Inconclusive
    // with a consumption profile — never acceptance, never rejection — and
    // the exact budget boundary is sharp: steps==S accepts, steps==S-1 is
    // typed exhaustion. Deterministic consumption makes S well-defined.
    let subject = prep
        .items
        .iter()
        .find(|item| {
            if !matches!(item.info, ConstantInfo::Defn(_)) {
                return false;
            }
            let v = fln_kernel::check(&item.env, &item.decl, budget);
            matches!(&v, Outcome::Complete(Verdict::Accepted { consumption })
                if consumption.steps_used >= 50 && consumption.max_depth >= 4)
        })
        .expect("a real accepted definition with measurable consumption");
    let baseline = fln_kernel::check(&subject.env, &subject.decl, budget);
    let Outcome::Complete(Verdict::Accepted {
        consumption: base_cost,
    }) = baseline
    else {
        panic!("baseline must accept");
    };
    let s = base_cost.steps_used;
    let root_before = subject.env.logical_root(&options).to_string();
    eprintln!(
        "fault_matrix resource subject: {} steps={} depth={}",
        subject.lead.to_display_string(),
        s,
        base_cost.max_depth
    );

    // Exact-limit acceptance: budget == consumption is enough.
    {
        let start_us = emit.started.elapsed().as_micros();
        let exact = Budget {
            steps: s,
            depth: budget.depth,
        };
        let v = fln_kernel::check(&subject.env, &subject.decl, exact);
        let (actual, class, _msg, steps_used, max_depth) = verdict_facts(&v);
        let ok = actual == "accepted" && steps_used == s;
        emit.fault_row(
            "resource_boundary_exact_accept",
            None,
            &subject.lead.to_display_string(),
            "accepted",
            &actual,
            class.as_deref(),
            "",
            exact,
            steps_used,
            max_depth,
            &root_before,
            &root_before,
            true,
            None,
            if ok { "pass" } else { "fail" },
            "exact-budget-boundary-accepts",
            start_us,
        );
        assert!(
            ok,
            "exact-limit budget must accept: {actual} steps={steps_used}"
        );
    }

    // One-under: typed Inconclusive{Steps}, never a verdict about the term.
    {
        let start_us = emit.started.elapsed().as_micros();
        let under = Budget {
            steps: s - 1,
            depth: budget.depth,
        };
        let v = fln_kernel::check(&subject.env, &subject.decl, under);
        let (actual, class, _msg, steps_used, max_depth) = verdict_facts(&v);
        let ok = matches!(
            resource_exhaustion(&v),
            Some(ResourceUsage {
                reason: ResourceReason::Heartbeats { consumed, limit },
                allowed,
                observed,
            }) if *consumed == *observed
                && *limit == under.steps
                && *allowed == under.steps
                && *observed > *allowed
        );
        let root_after = subject.env.logical_root(&options).to_string();
        emit.fault_row(
            "resource_exhaustion_steps",
            None,
            &subject.lead.to_display_string(),
            "inconclusive:Steps",
            &actual,
            class.as_deref(),
            "",
            under,
            steps_used,
            max_depth,
            &root_before,
            &root_after,
            root_before == root_after,
            None,
            if ok { "pass" } else { "fail" },
            "exhaustion-typed-not-a-verdict",
            start_us,
        );
        assert!(
            ok,
            "one-under budget must be Inconclusive{{Steps}}: {actual}"
        );
    }

    // Depth exhaustion: a shallow depth budget is typed Inconclusive{Depth}.
    {
        let start_us = emit.started.elapsed().as_micros();
        let shallow = Budget {
            steps: budget.steps,
            depth: 2,
        };
        let v = fln_kernel::check(&subject.env, &subject.decl, shallow);
        let (actual, class, _msg, steps_used, max_depth) = verdict_facts(&v);
        let ok = matches!(
            resource_exhaustion(&v),
            Some(ResourceUsage {
                reason: ResourceReason::RecursionDepth { limit },
                allowed,
                observed,
            }) if *limit == u64::from(shallow.depth)
                && *allowed == u64::from(shallow.depth)
                && *observed > *allowed
        );
        emit.fault_row(
            "resource_exhaustion_depth",
            None,
            &subject.lead.to_display_string(),
            "inconclusive:Depth",
            &actual,
            class.as_deref(),
            "",
            shallow,
            steps_used,
            max_depth,
            &root_before,
            &root_before,
            true,
            None,
            if ok { "pass" } else { "fail" },
            "depth-exhaustion-typed",
            start_us,
        );
        assert!(
            ok,
            "shallow depth budget must be Inconclusive{{Depth}}: {actual}"
        );
    }

    // Recovery: the same declaration under the default budget accepts again
    // with byte-identical resource facts — exhaustion left nothing behind.
    {
        let start_us = emit.started.elapsed().as_micros();
        let v = fln_kernel::check(&subject.env, &subject.decl, budget);
        let (actual, class, _msg, steps_used, max_depth) = verdict_facts(&v);
        let ok = actual == "accepted" && steps_used == s && max_depth == base_cost.max_depth;
        let root_after = subject.env.logical_root(&options).to_string();
        emit.fault_row(
            "resource_recovery",
            None,
            &subject.lead.to_display_string(),
            "accepted",
            &actual,
            class.as_deref(),
            "",
            budget,
            steps_used,
            max_depth,
            &root_before,
            &root_after,
            root_before == root_after,
            Some(&actual),
            if ok { "pass" } else { "fail" },
            "recovery-byte-identical-consumption",
            start_us,
        );
        assert!(
            ok,
            "recovery must reproduce the baseline exactly: {actual} steps={steps_used} (want {s})"
        );
    }
}
