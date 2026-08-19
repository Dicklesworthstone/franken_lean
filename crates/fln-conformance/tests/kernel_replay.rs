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
//! Evidence discipline (the ap6 acceptance contract): the PRELUDE replay
//! (`prelude_replays_through_the_kernel`) runs a deterministic {1, 8, 32}
//! worker-thread matrix. Environment construction is canonical (module-order
//! Kahn) and shared; each unit is checked against the O(1) environment
//! snapshot it would see in the sequential replay, so the authoritative
//! verdict stream — classes, diagnostics, and consumption — is
//! schedule-independent by construction, and the matrix PROVES it byte-equal
//! at every width on that input.
//!
//! **The per-commit matrix does not cover the corpus** (beads `fln-8zsq`,
//! `fln-corpus-thread-matrix-93te`). The corpus differential
//! (`pinned_present_olean_kernel_differential`) scores verdicts at a single
//! explicitly pinned width and compares no digests across widths at all. The
//! cross-width comparison is a separate lane,
//! `present_olean_corpus_thread_matrix_compares_stream_digests`, which replays
//! the same reconstructed environments at every width in
//! `CORPUS_MATRIX_WIDTHS` and names the diverging pair and unit if they ever
//! disagree.
//!
//! What that lane earns is bounded and is stated where it is claimed: it is
//! `#[ignore]`d for cost and SKIPs typed without the pin, so a green run is ONE
//! OBSERVATION at one corpus revision, pin and host — class `bounded_model`,
//! never `invariant`. PG-5 asks for {1, 8, 32} PER COMMIT; an on-demand lane is
//! a DOCUMENTED SHORTFALL against that gate rather than compliance with it, and
//! D7 forbids the observation standing in for the invariant.
//!
//! Machine rows go to stdout as schema-versioned NDJSON
//! (`fln.e2e.kernel-admission`/`fln.e2e.kernel-admission-fault`, validated by
//! `scripts/evidence.py validate-kernel-admission`); human logs stay on
//! stderr — the two streams must never merge.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fs;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use fln_conformance::pin;
use fln_core::diag::{ResourceReason, StructuralUnit};
use fln_core::expr::{BinderInfo, Expr, ExprNode};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::{InconclusiveCause, Outcome, ResourceUsage};
use fln_env::constants::{
    ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, OpaqueVal, ReducibilityHints,
};
use fln_env::decl_closure::{
    self, DeclClosureBudget, DeclClosureInput, DeclClosureStatus, MissingConstantFinding,
};
use fln_env::environment::Environment;
use fln_hash::domain::{Domain, hash};
use fln_kernel::Declaration;
use fln_kernel::verdict::{Budget, ExecConfig, StackMeasurement, Verdict};
use fln_olean::decl::DeclDecoder;
use fln_olean::format;
use fln_olean::region::{OleanView, WalkBudget};
use fln_olean::write::{ModuleWriteInput, OleanWriteHeader, WriteBudget, encode_module};

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
/// the pin's two-phase path, partial definitions the safe path). Inductive and
/// quotient members are assembled into their block envelopes by
/// `prepare_replay_from`; every remaining singleton kind has a kernel envelope.
fn as_declaration(info: &ConstantInfo) -> Option<Declaration> {
    match info {
        ConstantInfo::Axiom(v) => Some(Declaration::Axiom(v.clone())),
        ConstantInfo::Thm(v) => Some(Declaration::Thm(v.clone())),
        ConstantInfo::Defn(v) => Some(Declaration::Defn(v.clone())),
        ConstantInfo::Opaque(v) => Some(Declaration::Opaque(v.clone())),
        _ => None,
    }
}

#[test]
fn singleton_opaque_reaches_the_existing_kernel_admission_envelope() {
    let name = Name::str(Name::anonymous(), "opaqueAdapterProbe");
    let opaque = OpaqueVal {
        base: ConstantVal {
            name: name.clone(),
            level_params: Vec::new(),
            type_: Expr::sort(fln_core::level::Level::zero()),
        },
        value: Expr::sort(fln_core::level::Level::zero()),
        is_unsafe: false,
        all: vec![name],
    };

    assert_eq!(
        as_declaration(&ConstantInfo::Opaque(opaque.clone())),
        Some(Declaration::Opaque(opaque)),
        "the replay adapter must not bypass the kernel's existing opaque admission rule"
    );
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
    member_names: Vec<Name>,
    member_indices: Vec<usize>,
    kind: &'static str,
    members: u64,
    env: Environment,
    decl: Declaration,
    info: ConstantInfo,
}

struct PreparedReplay {
    items: Vec<WorkItem>,
    unchecked: BTreeMap<&'static str, u64>,
    /// Decoded rows that cannot be submitted as fresh declarations in the
    /// supplied fixture environment (most commonly duplicate theorem rows
    /// collapsed by the Reference replay's `HashMap`). They are never counted
    /// as compared: the Reference did not issue a second kernel verdict.
    context_unscorable: Vec<(usize, Name, &'static str)>,
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
    prepare_replay_from(Environment::new(), None, infos, true)
}

/// Corpus-scale variant of [`prepare_replay`]. The supplied environment is a
/// decoded Reference import environment used only as Tribunal fixture context:
/// declarations under test still go through `fln_kernel::check`, and no result
/// from this harness is an authority to admit a declaration in production.
fn prepare_replay_from(
    mut env: Environment,
    reference_context: Option<&ReferenceFixtureContext>,
    infos: &[ConstantInfo],
    emit_order_summary: bool,
) -> PreparedReplay {
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
    if emit_order_summary {
        eprintln!(
            "kernel_replay order: {} units over {} declarations \
             ({} topologically sorted, {} in dependency cycles replayed last)",
            units.len(),
            infos.len(),
            order.len(),
            cyclic.len()
        );
    }

    let mut items: Vec<WorkItem> = Vec::new();
    let mut unchecked: BTreeMap<&'static str, u64> = BTreeMap::new();
    let mut context_unscorable = Vec::new();
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
        let has_existing_member = unit
            .members
            .iter()
            .any(|member| env.find(infos[*member].name()).is_some());
        if has_existing_member {
            for &member in &unit.members {
                let reason = match env.find(infos[member].name()) {
                    Some(existing)
                        if reference_replay_duplicate(
                            reference_context
                                .and_then(|context| context.representative(infos[member].name()))
                                .unwrap_or(existing),
                            &infos[member],
                        ) =>
                    {
                        "reference_replay_duplicate_theorem"
                    }
                    Some(_) => "decoded_name_collision_in_fixture_context",
                    None => "admission_unit_contains_context_collision",
                };
                context_unscorable.push((member, infos[member].name().clone(), reason));
            }
            continue;
        }
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
            member_names: unit
                .members
                .iter()
                .map(|member| infos[*member].name().clone())
                .collect(),
            member_indices: unit.members.clone(),
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
        context_unscorable,
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

/// The first divergence across runs at different widths, or `None` when the
/// authoritative streams and their consumption are identical (R3 of bead
/// `fln-corpus-thread-matrix-93te`).
///
/// Extracted so the corpus matrix (R2) reuses this rather than growing a second
/// comparison that could drift from the Prelude's.
///
/// Every run is compared against the first. Equality is transitive, so baseline-vs-rest
/// reaches the same conclusion as all-pairs; the REPORT nonetheless names BOTH widths,
/// because "threads=8 diverged" does not say what it diverged from, and a three-width
/// matrix has three candidate baselines. That is the scope-the-evidence-to-the-site rule
/// applied to a diagnostic.
///
/// Differing unit COUNTS are named explicitly. The inline version this replaces zipped
/// the two streams, and `zip` stops at the shorter side — so a run that dropped units
/// outright compared equal on every position it did have and was reported as "digest
/// mismatch with equal prefixes", which describes the symptom and hides the cause.
fn first_divergence_across_widths(runs: &[MatrixRun]) -> Option<String> {
    let baseline = runs.first()?;
    for run in &runs[1..] {
        if run.stream_digest != baseline.stream_digest {
            if run.outcomes.len() != baseline.outcomes.len() {
                return Some(format!(
                    "threads={} vs threads={}: unit count differs, {} vs {}",
                    baseline.threads,
                    run.threads,
                    baseline.outcomes.len(),
                    run.outcomes.len()
                ));
            }
            for (index, (a, b)) in baseline
                .outcomes
                .iter()
                .zip(run.outcomes.iter())
                .enumerate()
            {
                if a != b {
                    return Some(format!(
                        "threads={} vs threads={}: unit={} lead={}: {} vs {}",
                        baseline.threads, run.threads, index, a.lead, a.outcome, b.outcome
                    ));
                }
            }
            return Some(format!(
                "threads={} vs threads={}: digest mismatch over identical unit streams",
                baseline.threads, run.threads
            ));
        }
        if run.steps_total != baseline.steps_total || run.depth_max != baseline.depth_max {
            return Some(format!(
                "threads={} vs threads={}: consumption differs, steps {} vs {}, depth {} vs {}",
                baseline.threads,
                run.threads,
                baseline.steps_total,
                run.steps_total,
                baseline.depth_max,
                run.depth_max
            ));
        }
    }
    None
}

// Rust's default spawned-thread stack is 2 MiB on this target. That is below
// the depth at which `Budget::DEFAULT` can still permit the kernel to recurse,
// so inheriting it lets a valid deep term abort the whole Tribunal before the
// kernel can return a typed depth-exhaustion outcome (franken_lean-kxbj).
//
// The floor is now the kernel's own stated requirement rather than a number
// chosen here: `Budget::MIN_STACK_BYTES` is what `Budget::DEFAULT` (which this
// harness passes) needs, derived from the measured per-depth stack cost. Bound
// to the constant rather than copied from it so the two cannot drift apart —
// the previous hand-written 16 MiB was empirically adequate for today's corpus
// but below the measured worst case for the default depth policy.
const KERNEL_REPLAY_WORKER_STACK_BYTES: usize = Budget::MIN_STACK_BYTES;

fn unit_outcome(item: &WorkItem, verdict: &Outcome<Verdict>) -> UnitOutcome {
    let (outcome, class, message, steps_used, max_depth) = verdict_facts(verdict);
    let outcome = match class {
        Some(class) => format!("{outcome}:{class}"),
        None => outcome,
    };
    UnitOutcome {
        lead: item.lead.to_display_string(),
        kind: item.kind,
        members: item.members,
        outcome,
        message,
        steps_used,
        max_depth,
    }
}

/// Run one selected real-corpus admission unit on an explicit stack contract.
/// The resource probe below must not accidentally inherit Rust's smaller
/// default spawned-thread stack and turn a typed depth result into a process
/// abort.
fn check_work_item_with_stack(
    item: &WorkItem,
    budget: Budget,
    stack_bytes: usize,
) -> Outcome<Verdict> {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("fln-kernel-resource-probe".to_string())
            .stack_size(stack_bytes)
            .spawn_scoped(scope, || fln_kernel::check(&item.env, &item.decl, budget))
            .expect("spawn selected kernel replay worker with the explicit stack contract")
            .join()
            .expect("selected kernel replay worker must not panic")
    })
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
        let mut workers = Vec::with_capacity(threads);
        for worker_index in 0..threads {
            workers.push(
                std::thread::Builder::new()
                    .name(format!("fln-kernel-replay-{worker_index}"))
                    .stack_size(KERNEL_REPLAY_WORKER_STACK_BYTES)
                    .spawn_scoped(scope, || {
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
                    })
                    .expect("spawn kernel replay worker with the explicit stack contract"),
            );
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
        let outcome = unit_outcome(item, verdict);
        steps_total = steps_total.saturating_add(outcome.steps_used);
        depth_max = depth_max.max(outcome.max_depth);
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
             \"parity_ledger_row\":\"not_applicable_kernel_admission_replay\",\
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

// ---------------------------------------------------------------------------
// Present-olean Reference-kernel corpus (beads fln-lst4 / fln-7odd).
// ---------------------------------------------------------------------------

/// Floors are deliberately inequalities, not golden equality pins: adding a
/// module at the same Reference epoch may increase coverage, while silently
/// enumerating or decoding less than the measured pin must fail.
const PINNED_PRESENT_OLEAN_FLOOR: u64 = 2_433;
const PINNED_DECODED_DECL_FLOOR: u64 = 215_136;
const PINNED_ORACLE_APPLICABLE_FLOOR: u64 = 211_524;
/// Anti-vacuity floor for the retained v1 matrix observation. That observation
/// predates module-part decoding and therefore measured the 158,608 declarations
/// visible in public `.olean` regions. It remains historical bounded-model evidence,
/// not a claim about the current decoder; `lane_source_digest_at_run` is explicitly
/// provenance rather than a freshness gate. New matrix runs still have to clear the
/// current `PINNED_DECODED_DECL_FLOOR` before they can publish a receipt.
const RETAINED_MATRIX_V1_DECODED_DECL_FLOOR: u64 = 158_608;
/// The single, explicitly pinned worker count the corpus census is produced at
/// (R1 of bead `fln-corpus-thread-matrix-93te`).
///
/// This replaced a size heuristic under which two modules of different sizes ran at
/// different widths, so the census was not produced at one consistent configuration —
/// and runs that were not produced under comparable configurations cannot support a
/// determinism claim at all. Pinning is therefore a prerequisite for the matrix, not a
/// substitute for it: one pinned width still compares no stream digests ACROSS widths,
/// so the census's own numbers say nothing about schedules in either direction. The
/// comparison across widths is `CORPUS_MATRIX_WIDTHS` and its lane, whose class is
/// bounded by what an on-demand run can earn.
const CORPUS_CENSUS_WIDTH: usize = 8;
/// The widths PG-5 names, and the widths the corpus thread matrix actually runs
/// (R2 of bead `fln-corpus-thread-matrix-93te`).
///
/// Spelled out rather than derived. `CORPUS_CENSUS_WIDTH` must be one of these, so the
/// census's own run is the matrix's middle column rather than a fourth, unrelated
/// configuration — but writing that constant INTO the array would invert the dependency:
/// repinning the census width would then silently move the matrix off the widths PG-5
/// names, while every `{1, 8, 32}` line in the documents stayed green. The relationship is
/// therefore CHECKED, at compile time, and the widths are the literal ones being claimed.
const CORPUS_MATRIX_WIDTHS: [usize; 3] = [1, 8, 32];
const _: () = assert!(
    CORPUS_MATRIX_WIDTHS[1] == CORPUS_CENSUS_WIDTH,
    "the corpus census must be scored at one of the matrix's widths, or its run is a \
     configuration the matrix never compared"
);
const MAX_PINNED_OLEAN_BYTES: u64 = 512 * 1024 * 1024;
const DEFAULT_LEANCHECKER_TIMEOUT: Duration = Duration::from_secs(300);
/// Stock leanchecker expands every prefix, launches one task per matching
/// module, and only then joins the tasks. The absent `Mathlib` namespace root
/// used to expand to all 8,264 modules at once: the pinned process exceeded 30
/// minutes and peaked above 150 GiB RSS. Even a 139-module AlgebraicGeometry
/// prefix peaked at 186 GiB. The whole-corpus lane therefore gives an exact
/// module list to the Tribunal driver, which runs eight replay tasks at a time,
/// while these outer batches retain bounded deadlines and durable resume
/// points. The 256 is a checkpoint/process interval, not the concurrency.
const WHOLE_MATHLIB_ORACLE_MODULES_PER_PROCESS: usize = 256;
const WHOLE_MATHLIB_ORACLE_PROCESS_TIMEOUT: Duration = Duration::from_secs(30 * 60);
const WHOLE_MATHLIB_ORACLE_TOTAL_TIMEOUT: Duration = Duration::from_secs(4 * 60 * 60);
const ORACLE_OUTPUT_LIMIT: usize = 8 * 1024 * 1024;

#[derive(Clone)]
struct CorpusModule {
    name: String,
    path: PathBuf,
    olean_hash: String,
    imports: BTreeSet<String>,
    decoded: u64,
    oracle_skipped: u64,
}

struct CorpusInventory {
    modules: BTreeMap<String, CorpusModule>,
    decoded: u64,
    oracle_skipped: u64,
    missing_imports: Vec<(String, String)>,
    fixture_hash: String,
}

/// This mirrors the exact filter in the pinned `Lean.Replay.replay`, rather
/// than inferring oracle authority from a successful process exit. The
/// Reference deliberately does not submit unsafe or partial constants to its
/// kernel; those rows therefore have no oracle verdict and are unscorable.
fn reference_replay_skips(info: &ConstantInfo) -> bool {
    match info {
        ConstantInfo::Axiom(value) => value.is_unsafe,
        ConstantInfo::Defn(value) => value.safety != DefinitionSafety::Safe,
        ConstantInfo::Thm(_) | ConstantInfo::Quot(_) => false,
        ConstantInfo::Opaque(value) => value.is_unsafe,
        ConstantInfo::Induct(value) => value.is_unsafe,
        ConstantInfo::Ctor(value) => value.is_unsafe,
        ConstantInfo::Rec(value) => value.is_unsafe,
    }
}

fn collect_present_oleans(dir: &Path, paths: &mut Vec<PathBuf>) -> Result<(), String> {
    let mut entries = fs::read_dir(dir)
        .map_err(|error| format!("read corpus directory {}: {error}", dir.display()))?
        .collect::<Result<Vec<_>, _>>()
        .map_err(|error| format!("enumerate corpus directory {}: {error}", dir.display()))?;
    entries.sort_by_key(std::fs::DirEntry::file_name);
    for entry in entries {
        let path = entry.path();
        let file_type = entry
            .file_type()
            .map_err(|error| format!("stat corpus entry {}: {error}", path.display()))?;
        if file_type.is_symlink() {
            return Err(format!(
                "present-olean corpus refuses symlink entry {}",
                path.display()
            ));
        }
        if file_type.is_dir() {
            collect_present_oleans(&path, paths)?;
        } else if file_type.is_file()
            && path.extension().and_then(|extension| extension.to_str()) == Some("olean")
        {
            paths.push(path);
        }
    }
    Ok(())
}

fn module_name_from_path(root: &Path, path: &Path) -> Result<String, String> {
    let relative = path
        .strip_prefix(root)
        .map_err(|error| format!("{} is outside {}: {error}", path.display(), root.display()))?
        .with_extension("");
    let mut parts = Vec::new();
    for component in relative.components() {
        let std::path::Component::Normal(part) = component else {
            return Err(format!(
                "non-normal module path component in {}",
                relative.display()
            ));
        };
        let part = part
            .to_str()
            .ok_or_else(|| format!("non-UTF-8 module path {}", relative.display()))?;
        if part.is_empty() {
            return Err(format!(
                "empty module path component in {}",
                relative.display()
            ));
        }
        parts.push(part);
    }
    if parts.is_empty() {
        return Err(format!("empty module name for {}", path.display()));
    }
    Ok(parts.join("."))
}

fn tagged_fixture_hash(tag: &[u8], fields: &[&[u8]]) -> String {
    let mut preimage = Vec::new();
    preimage.extend_from_slice(tag);
    preimage.push(0);
    for field in fields {
        preimage.extend_from_slice(&u64::try_from(field.len()).unwrap_or(u64::MAX).to_le_bytes());
        preimage.extend_from_slice(field);
    }
    hash(Domain::Fixture, &preimage).to_hex()
}

struct DecodedCorpusModule {
    infos: Vec<ConstantInfo>,
    imports: BTreeSet<String>,
    olean_hash: String,
}

fn read_corpus_module_part(path: &Path) -> Result<Vec<u8>, String> {
    let metadata =
        fs::metadata(path).map_err(|error| format!("stat {}: {error}", path.display()))?;
    if metadata.len() > MAX_PINNED_OLEAN_BYTES {
        return Err(format!(
            "{} is {} bytes, over the {}-byte corpus cap",
            path.display(),
            metadata.len(),
            MAX_PINNED_OLEAN_BYTES
        ));
    }
    fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))
}

fn corpus_module_parts_hash(name: &str, parts: &[(&str, &[u8])]) -> String {
    let mut fields = Vec::with_capacity(1 + parts.len() * 2);
    fields.push(name.as_bytes());
    for (level, bytes) in parts {
        fields.push(level.as_bytes());
        fields.push(*bytes);
    }
    tagged_fixture_hash(b"fln.kernel-reference-corpus.olean-parts/2", &fields)
}

/// Decode the exact module-data level Lean imports under `import all`.
///
/// A module-system `.olean` is only the exported part. The server and private
/// sidecars are compacted against the earlier regions, and the private part is
/// the one whose constant array retains private auxiliaries and definition
/// bodies. Reading only the public file silently postulated exported
/// definitions as axioms and omitted the equation compiler's private family.
fn decode_corpus_module(path: &Path, name: &str) -> Result<DecodedCorpusModule, String> {
    let public = read_corpus_module_part(path)?;
    let public_view =
        OleanView::parse(&public).map_err(|error| format!("parse {}: {error}", path.display()))?;
    let module_data = public_view
        .module_data(WalkBudget::default())
        .map_err(|error| format!("module data {}: {error}", path.display()))?;
    let imports = module_data
        .imports
        .iter()
        .map(|import| import.module.to_display_string())
        .collect::<BTreeSet<_>>();

    if !module_data.is_module {
        let infos = DeclDecoder::new(&public_view, WalkBudget::default())
            .decode_module_constants()
            .map_err(|error| format!("decode {}: {error}", path.display()))?;
        let olean_hash = corpus_module_parts_hash(name, &[("exported", &public)]);
        return Ok(DecodedCorpusModule {
            infos,
            imports,
            olean_hash,
        });
    }

    let server_path = path.with_extension("olean.server");
    let private_path = path.with_extension("olean.private");
    let server = read_corpus_module_part(&server_path)?;
    let private = read_corpus_module_part(&private_path)?;
    let total_bytes = public
        .len()
        .checked_add(server.len())
        .and_then(|total| total.checked_add(private.len()))
        .ok_or_else(|| format!("module-part byte count overflow for {name}"))?;
    if total_bytes as u64 > MAX_PINNED_OLEAN_BYTES {
        return Err(format!(
            "module parts for {name} total {total_bytes} bytes, over the {}-byte corpus cap",
            MAX_PINNED_OLEAN_BYTES
        ));
    }
    let private_view =
        OleanView::parse_with_dependencies(&private, &[&public, &server]).map_err(|error| {
            format!(
                "parse {} with module dependencies: {error}",
                private_path.display()
            )
        })?;
    let infos = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .map_err(|error| format!("decode {}: {error}", private_path.display()))?;
    let olean_hash = corpus_module_parts_hash(
        name,
        &[
            ("exported", &public),
            ("server", &server),
            ("private", &private),
        ],
    );
    Ok(DecodedCorpusModule {
        infos,
        imports,
        olean_hash,
    })
}

fn qualify_module_name(module_prefix: Option<&str>, relative_name: String) -> String {
    module_prefix
        .map(|prefix| format!("{prefix}.{relative_name}"))
        .unwrap_or(relative_name)
}

/// Inventory oleans below one library root. `module_prefix` qualifies the
/// filesystem-relative name before it is compared against imports recorded in
/// the olean; Mathlib's root is nested below its namespace while the Reference
/// library root is not.
fn inventory_oleans(root: &Path, module_prefix: Option<&str>) -> Result<CorpusInventory, String> {
    let mut paths = Vec::new();
    collect_present_oleans(root, &mut paths)?;
    paths.sort();
    let mut modules = BTreeMap::new();
    let mut decoded = 0_u64;
    let mut oracle_skipped = 0_u64;
    let mut aggregate = Vec::new();
    aggregate.extend_from_slice(b"fln.kernel-reference-corpus.inventory/1\0");
    for path in paths {
        let relative_name = module_name_from_path(root, &path)?;
        let name = qualify_module_name(module_prefix, relative_name);
        let decoded_module = decode_corpus_module(&path, &name)?;
        let infos = decoded_module.infos;
        let decoded_here = u64::try_from(infos.len())
            .map_err(|_| format!("declaration count overflow in {}", path.display()))?;
        let skipped_here = infos
            .iter()
            .filter(|info| reference_replay_skips(info))
            .count() as u64;
        let olean_hash = decoded_module.olean_hash;
        let imports = decoded_module.imports;
        let module = CorpusModule {
            name: name.clone(),
            path,
            olean_hash: olean_hash.clone(),
            imports,
            decoded: decoded_here,
            oracle_skipped: skipped_here,
        };
        if modules.insert(name.clone(), module).is_some() {
            return Err(format!("duplicate present olean module {name}"));
        }
        decoded = decoded
            .checked_add(decoded_here)
            .ok_or_else(|| "decoded declaration census overflow".to_string())?;
        oracle_skipped = oracle_skipped
            .checked_add(skipped_here)
            .ok_or_else(|| "oracle-skipped declaration census overflow".to_string())?;
        aggregate.extend_from_slice(&(name.len() as u64).to_le_bytes());
        aggregate.extend_from_slice(name.as_bytes());
        aggregate.extend_from_slice(&(olean_hash.len() as u64).to_le_bytes());
        aggregate.extend_from_slice(olean_hash.as_bytes());
    }
    let present = modules.keys().cloned().collect::<BTreeSet<_>>();
    let mut missing_imports = Vec::new();
    for module in modules.values() {
        for import in module.imports.difference(&present) {
            missing_imports.push((module.name.clone(), import.clone()));
        }
    }
    Ok(CorpusInventory {
        modules,
        decoded,
        oracle_skipped,
        missing_imports,
        fixture_hash: hash(Domain::Fixture, &aggregate).to_hex(),
    })
}

fn inventory_present_oleans(root: &Path) -> Result<CorpusInventory, String> {
    inventory_oleans(root, None)
}

fn module_names_below(root: &Path, module_prefix: Option<&str>) -> Result<Vec<String>, String> {
    let mut paths = Vec::new();
    collect_present_oleans(root, &mut paths)?;
    paths.sort();
    paths
        .into_iter()
        .map(|path| {
            module_name_from_path(root, &path)
                .map(|relative| qualify_module_name(module_prefix, relative))
        })
        .collect()
}

#[test]
fn mathlib_olean_paths_are_qualified_before_import_matching() {
    assert_eq!(
        qualify_module_name(Some("Mathlib"), "Algebra.Group.Defs".to_string()),
        "Mathlib.Algebra.Group.Defs",
        "Mathlib's olean root sits below its namespace, unlike the Reference library root"
    );
    assert_eq!(
        qualify_module_name(None, "Std.Data.HashMap.Basic".to_string()),
        "Std.Data.HashMap.Basic",
        "the Reference library's names are already rooted at their on-disk namespace"
    );
}

fn corpus_module_order(inventory: &CorpusInventory) -> Result<Vec<String>, String> {
    let present = inventory
        .modules
        .keys()
        .cloned()
        .collect::<BTreeSet<String>>();
    let mut indegree = BTreeMap::<String, usize>::new();
    let mut dependents = BTreeMap::<String, BTreeSet<String>>::new();
    for module in inventory.modules.values() {
        let imports = module
            .imports
            .intersection(&present)
            .filter(|import| *import != &module.name)
            .cloned()
            .collect::<BTreeSet<_>>();
        indegree.insert(module.name.clone(), imports.len());
        for import in imports {
            dependents
                .entry(import)
                .or_default()
                .insert(module.name.clone());
        }
    }
    let mut ready = indegree
        .iter()
        .filter_map(|(name, degree)| (*degree == 0).then_some(name.clone()))
        .collect::<BTreeSet<_>>();
    let mut order = Vec::with_capacity(inventory.modules.len());
    while let Some(name) = ready.iter().next().cloned() {
        ready.remove(&name);
        order.push(name.clone());
        if let Some(next) = dependents.get(&name) {
            for dependent in next {
                let degree = indegree
                    .get_mut(dependent)
                    .expect("dependent module has an indegree row");
                *degree -= 1;
                if *degree == 0 {
                    ready.insert(dependent.clone());
                }
            }
        }
    }
    if order.len() != inventory.modules.len() {
        let cyclic = indegree
            .into_iter()
            .filter_map(|(name, degree)| (degree != 0).then_some(name))
            .take(20)
            .collect::<Vec<_>>();
        return Err(format!(
            "present-olean import graph contains a cycle or unresolved edge: {cyclic:?}"
        ));
    }
    Ok(order)
}

#[derive(Debug)]
enum ReferenceCorpusVerdict {
    Accepted {
        duration: Duration,
        stdout: String,
        stderr: String,
    },
    Rejected {
        status: ExitStatus,
        duration: Duration,
        stdout: String,
        stderr: String,
    },
    NoAnswer {
        reason: String,
        duration: Duration,
        stdout: String,
        stderr: String,
    },
}

fn read_capped(mut input: impl Read, limit: usize) -> std::io::Result<(Vec<u8>, bool)> {
    let mut kept = Vec::new();
    let mut truncated = false;
    let mut chunk = [0_u8; 16 * 1024];
    loop {
        let read = input.read(&mut chunk)?;
        if read == 0 {
            break;
        }
        let room = limit.saturating_sub(kept.len());
        let take = room.min(read);
        kept.extend_from_slice(&chunk[..take]);
        truncated |= take != read;
    }
    Ok((kept, truncated))
}

fn bounded_text(bytes: Vec<u8>, truncated: bool) -> String {
    let mut text = String::from_utf8_lossy(&bytes).into_owned();
    if truncated {
        text.push_str("\n[output truncated by fln-lst4 bound]\n");
    }
    text
}

fn leanchecker_path(reference_lib: &Path) -> Result<PathBuf, String> {
    let toolchain = reference_lib
        .parent()
        .and_then(Path::parent)
        .ok_or_else(|| {
            format!(
                "Reference library {} has no toolchain root",
                reference_lib.display()
            )
        })?;
    let path = toolchain.join("bin/leanchecker");
    path.is_file()
        .then_some(path.clone())
        .ok_or_else(|| format!("pinned leanchecker not found at {}", path.display()))
}

fn component_prefix(prefix: &str, module: &str) -> bool {
    let prefix = prefix.split('.').collect::<Vec<_>>();
    let module = module.split('.').collect::<Vec<_>>();
    prefix.len() <= module.len() && prefix.iter().zip(module.iter()).all(|(a, b)| a == b)
}

/// Compact target set for leanchecker's prefix-matching CLI. A top-level
/// zero-declaration umbrella is replaced by its immediate children; this
/// avoids the pin's packaging-only root failures without expanding the CLI to
/// one target per leaf (leanchecker rescans every olean for every target).
fn leanchecker_targets_for_required(
    inventory: &CorpusInventory,
    required_modules: &[&str],
) -> Vec<String> {
    let mut candidates = BTreeSet::new();
    for module in required_modules {
        let components = module.split('.').collect::<Vec<_>>();
        let top = components[0];
        let width = match inventory.modules.get(top) {
            Some(exact) if exact.decoded == 0 && components.len() > 1 => 2,
            _ => 1,
        };
        candidates.insert(components[..width].join("."));
    }
    let mut selected = Vec::<String>::new();
    for candidate in candidates {
        if !selected
            .iter()
            .any(|prefix| component_prefix(prefix, &candidate))
        {
            selected.push(candidate);
        }
    }
    selected
}

fn leanchecker_targets(inventory: &CorpusInventory) -> Vec<String> {
    let required_modules = inventory
        .modules
        .values()
        .filter(|module| module.decoded != 0)
        .map(|module| module.name.as_str())
        .collect::<Vec<_>>();
    leanchecker_targets_for_required(inventory, &required_modules)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LeancheckerBatchMode {
    Prefix,
    Exact,
}

impl LeancheckerBatchMode {
    fn label(self) -> &'static str {
        match self {
            Self::Prefix => "prefix",
            Self::Exact => "exact",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LeancheckerBatch {
    targets: Vec<String>,
    matched_modules: usize,
    mode: LeancheckerBatchMode,
}

impl LeancheckerBatch {
    fn covers_module(&self, module: &str) -> bool {
        match self.mode {
            LeancheckerBatchMode::Prefix => self
                .targets
                .iter()
                .any(|target| component_prefix(target, module)),
            LeancheckerBatchMode::Exact => self.targets.iter().any(|target| target == module),
        }
    }
}

fn leanchecker_batches_for_required(
    inventory: &CorpusInventory,
    required_modules: &[&str],
    max_modules: usize,
) -> Result<Vec<LeancheckerBatch>, String> {
    if max_modules == 0 {
        return Err("leanchecker module batch size must be nonzero".to_string());
    }
    if max_modules == usize::MAX {
        let targets = leanchecker_targets_for_required(inventory, required_modules);
        if targets.is_empty() {
            return Err("present-olean corpus produced no declaration-bearing targets".to_string());
        }
        return Ok(vec![LeancheckerBatch {
            targets,
            matched_modules: inventory.modules.len(),
            mode: LeancheckerBatchMode::Prefix,
        }]);
    }

    if required_modules.is_empty() {
        return Err("present-olean corpus produced no declaration-bearing targets".to_string());
    }
    Ok(required_modules
        .chunks(max_modules)
        .map(|modules| LeancheckerBatch {
            targets: modules.iter().map(|module| (*module).to_string()).collect(),
            matched_modules: modules.len(),
            mode: LeancheckerBatchMode::Exact,
        })
        .collect())
}

fn leanchecker_batches(
    inventory: &CorpusInventory,
    max_modules: usize,
) -> Result<Vec<LeancheckerBatch>, String> {
    let required_modules = inventory
        .modules
        .values()
        .filter(|module| module.decoded != 0)
        .map(|module| module.name.as_str())
        .collect::<Vec<_>>();
    leanchecker_batches_for_required(inventory, &required_modules, max_modules)
}

#[test]
fn finite_leanchecker_batches_are_exact_and_preserve_every_required_module() {
    let rows = [
        ("Mathlib.Algebra.A", 1_u64),
        ("Mathlib.Algebra.B", 1),
        ("Mathlib.Analysis.A", 1),
        ("Mathlib.Analysis.Empty", 0),
        ("Std", 1),
        ("Std.Data.A", 1),
        ("Std.Data.B", 1),
    ];
    let modules = rows
        .into_iter()
        .map(|(name, decoded)| {
            (
                name.to_string(),
                CorpusModule {
                    name: name.to_string(),
                    path: PathBuf::from(format!("{name}.olean")),
                    olean_hash: format!("hash-{name}"),
                    imports: BTreeSet::new(),
                    decoded,
                    oracle_skipped: 0,
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    let inventory = CorpusInventory {
        decoded: modules.values().map(|module| module.decoded).sum(),
        modules,
        oracle_skipped: 0,
        missing_imports: Vec::new(),
        fixture_hash: "batch-test".to_string(),
    };

    let batches = leanchecker_batches(&inventory, 2).expect("partition the synthetic corpus");
    assert_eq!(
        batches,
        [
            LeancheckerBatch {
                targets: vec![
                    "Mathlib.Algebra.A".to_string(),
                    "Mathlib.Algebra.B".to_string(),
                ],
                matched_modules: 2,
                mode: LeancheckerBatchMode::Exact,
            },
            LeancheckerBatch {
                targets: vec!["Mathlib.Analysis.A".to_string(), "Std".to_string()],
                matched_modules: 2,
                mode: LeancheckerBatchMode::Exact,
            },
            LeancheckerBatch {
                targets: vec!["Std.Data.A".to_string(), "Std.Data.B".to_string()],
                matched_modules: 2,
                mode: LeancheckerBatchMode::Exact,
            },
        ],
        "a finite batch must name modules exactly; prefix expansion is not a concurrency bound"
    );
    assert!(
        batches
            .iter()
            .flat_map(|batch| &batch.targets)
            .all(|target| target != "Mathlib"),
        "the absent Mathlib root would recreate the all-module task explosion"
    );
    assert!(batches.iter().all(|batch| {
        batch.mode == LeancheckerBatchMode::Exact && batch.targets.len() == batch.matched_modules
    }));

    let compact = leanchecker_batches(&inventory, usize::MAX)
        .expect("retain the ordinary corpus's compact one-process cover");
    assert_eq!(compact.len(), 1);
    assert_eq!(compact[0].targets, ["Mathlib", "Std"]);
    assert_eq!(compact[0].mode, LeancheckerBatchMode::Prefix);

    let pending_after_std_checkpoint = ["Std.Data.A", "Std.Data.B"];
    let resumed = leanchecker_batches_for_required(&inventory, &pending_after_std_checkpoint, 1)
        .expect("partition only declarations without complete oracle checkpoints");
    assert_eq!(
        resumed
            .iter()
            .flat_map(|batch| &batch.targets)
            .cloned()
            .collect::<Vec<_>>(),
        ["Std.Data.A", "Std.Data.B"],
        "a completed exact parent must not force all of its descendants back into one replay"
    );
    assert!(
        resumed
            .iter()
            .all(|batch| batch.mode == LeancheckerBatchMode::Exact)
    );
}

fn wait_for_child_with_timeout(
    child: &mut Child,
    started: Instant,
    timeout: Duration,
    process_name: &str,
) -> Result<(ExitStatus, bool), String> {
    loop {
        if let Some(status) = child
            .try_wait()
            .map_err(|error| format!("poll {process_name}: {error}"))?
        {
            return Ok((status, false));
        }
        if started.elapsed() >= timeout {
            child
                .kill()
                .map_err(|error| format!("kill timed-out {process_name}: {error}"))?;
            let status = child
                .wait()
                .map_err(|error| format!("reap timed-out {process_name}: {error}"))?;
            return Ok((status, true));
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

const LEANCHECKER_TIMEOUT_PROBE_CHILD_ENV: &str = "_FLN_TEST_LEANCHECKER_TIMEOUT_CHILD";

#[test]
fn leanchecker_timeout_probe_child() {
    if std::env::var_os(LEANCHECKER_TIMEOUT_PROBE_CHILD_ENV).is_none() {
        return;
    }
    loop {
        std::thread::park();
    }
}

#[test]
fn leanchecker_timeout_kills_and_reaps_the_child() {
    let executable = std::env::current_exe().expect("locate the current test binary");
    let mut child = Command::new(executable)
        .env_clear()
        .env(LEANCHECKER_TIMEOUT_PROBE_CHILD_ENV, "1")
        .arg("--exact")
        .arg("leanchecker_timeout_probe_child")
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .expect("spawn the non-answer timeout probe child");
    let started = Instant::now();
    let (status, timed_out) = wait_for_child_with_timeout(
        &mut child,
        started,
        Duration::from_millis(40),
        "timeout probe child",
    )
    .expect("kill and reap the timeout probe child");
    assert!(timed_out, "the non-answer timeout path was not exercised");
    assert!(
        !status.success(),
        "a killed oracle child cannot be acceptance"
    );
    assert!(
        started.elapsed() < Duration::from_secs(5),
        "the timeout probe did not remain promptly bounded"
    );
}

fn reference_lean_path(reference_lib: &Path) -> Result<PathBuf, String> {
    let toolchain = reference_lib
        .parent()
        .and_then(Path::parent)
        .ok_or_else(|| {
            format!(
                "Reference library {} has no toolchain root",
                reference_lib.display()
            )
        })?;
    let path = toolchain.join("bin/lean");
    path.is_file()
        .then_some(path.clone())
        .ok_or_else(|| format!("pinned lean not found at {}", path.display()))
}

fn exact_leanchecker_driver_path() -> Result<PathBuf, String> {
    let path =
        fln_conformance::checked_workspace_root!().join("scripts/tribunal/exact_leanchecker.lean");
    let metadata = fs::symlink_metadata(&path).map_err(|error| {
        format!(
            "stat exact-module Reference driver {}: {error}",
            path.display()
        )
    })?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(format!(
            "exact-module Reference driver {} must be a real file",
            path.display()
        ));
    }
    Ok(path)
}

fn configured_reference_command(binary: &Path, search_roots: &[&Path]) -> Result<Command, String> {
    let pinned_bin = binary
        .parent()
        .ok_or_else(|| format!("Reference binary {} has no bin directory", binary.display()))?;
    let lean_path = std::env::join_paths(search_roots)
        .map_err(|error| format!("construct pinned Reference search path: {error}"))?;
    let mut command = Command::new(binary); // ubs:ignore — path is derived from the SUITE.lock-pinned Reference installation.
    command
        .env_clear()
        // `Lean.findSysroot` invokes the sibling `lean --print-prefix` by
        // basename. Give it only the pinned bin directory, never ambient PATH.
        .env("PATH", pinned_bin)
        .env("LEAN_PATH", lean_path)
        .env("LC_ALL", "C")
        .env("LANG", "C")
        .env("TZ", "UTC")
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    Ok(command)
}

fn run_reference_replay_command(
    mut command: Command,
    binary: &Path,
    process_name: &str,
    timeout: Duration,
) -> Result<ReferenceCorpusVerdict, String> {
    let started = Instant::now();
    let mut child = command
        .spawn()
        .map_err(|error| format!("spawn {}: {error}", binary.display()))?;
    let stdout = child
        .stdout
        .take()
        .ok_or_else(|| format!("{process_name} stdout pipe missing"))?;
    let stderr = child
        .stderr
        .take()
        .ok_or_else(|| format!("{process_name} stderr pipe missing"))?;
    let stdout_reader = std::thread::spawn(move || read_capped(stdout, ORACLE_OUTPUT_LIMIT));
    let stderr_reader = std::thread::spawn(move || read_capped(stderr, ORACLE_OUTPUT_LIMIT));
    let (status, timed_out) =
        wait_for_child_with_timeout(&mut child, started, timeout, process_name)?;
    let (stdout_bytes, stdout_truncated) = stdout_reader
        .join()
        .map_err(|_| format!("{process_name} stdout reader panicked"))?
        .map_err(|error| format!("read {process_name} stdout: {error}"))?;
    let (stderr_bytes, stderr_truncated) = stderr_reader
        .join()
        .map_err(|_| format!("{process_name} stderr reader panicked"))?
        .map_err(|error| format!("read {process_name} stderr: {error}"))?;
    let stdout = bounded_text(stdout_bytes, stdout_truncated);
    let stderr = bounded_text(stderr_bytes, stderr_truncated);
    let duration = started.elapsed();
    if timed_out {
        return Ok(ReferenceCorpusVerdict::NoAnswer {
            reason: format!("{process_name} exceeded {} seconds", timeout.as_secs()),
            duration,
            stdout,
            stderr,
        });
    }
    if status.success() {
        return Ok(ReferenceCorpusVerdict::Accepted {
            duration,
            stdout,
            stderr,
        });
    }
    if status.code().is_none() {
        return Ok(ReferenceCorpusVerdict::NoAnswer {
            reason: format!("{process_name} terminated by signal: {status}"),
            duration,
            stdout,
            stderr,
        });
    }
    let packaging_or_setup = [
        "does not exist",
        "failed to read module data",
        "incompatible header",
        "Could not find any oleans",
        "Could not resolve module",
        "could not execute external process 'lean'",
    ]
    .iter()
    .any(|needle| stdout.contains(needle) || stderr.contains(needle));
    if packaging_or_setup {
        Ok(ReferenceCorpusVerdict::NoAnswer {
            reason: format!("{process_name} setup/artifact failure: {status}"),
            duration,
            stdout,
            stderr,
        })
    } else {
        Ok(ReferenceCorpusVerdict::Rejected {
            status,
            duration,
            stdout,
            stderr,
        })
    }
}

fn run_leanchecker_with_search_roots(
    reference_lib: &Path,
    search_roots: &[&Path],
    targets: &[String],
    timeout: Duration,
) -> Result<ReferenceCorpusVerdict, String> {
    let binary = leanchecker_path(reference_lib)?;
    let mut command = configured_reference_command(&binary, search_roots)?;
    command.arg("-v").args(targets);
    run_reference_replay_command(command, &binary, "leanchecker", timeout)
}

fn exact_completion_modules(stdout: &str) -> Result<BTreeSet<String>, String> {
    const PREFIX: &str = "replayed exact module ";
    let mut completed = BTreeSet::new();
    for module in stdout.lines().filter_map(|line| line.strip_prefix(PREFIX)) {
        if module.is_empty() {
            return Err("exact-module Reference driver emitted an empty completion".to_string());
        }
        if !completed.insert(module.to_string()) {
            return Err(format!(
                "exact-module Reference driver completed {module} more than once"
            ));
        }
    }
    Ok(completed)
}

fn validate_exact_completions(targets: &[String], stdout: &str) -> Result<(), String> {
    let expected = targets.iter().cloned().collect::<BTreeSet<_>>();
    if expected.len() != targets.len() {
        return Err("exact-module Reference request contains duplicate modules".to_string());
    }
    let completed = exact_completion_modules(stdout)?;
    if completed != expected {
        let missing = expected.difference(&completed).take(8).collect::<Vec<_>>();
        let unexpected = completed.difference(&expected).take(8).collect::<Vec<_>>();
        return Err(format!(
            "exact-module Reference completion mismatch: missing={missing:?} unexpected={unexpected:?}"
        ));
    }
    Ok(())
}

fn run_exact_leanchecker_with_search_roots(
    reference_lib: &Path,
    search_roots: &[&Path],
    targets: &[String],
    timeout: Duration,
) -> Result<ReferenceCorpusVerdict, String> {
    let binary = reference_lean_path(reference_lib)?;
    let driver = exact_leanchecker_driver_path()?;
    let mut command = configured_reference_command(&binary, search_roots)?;
    command.arg("--run").arg(driver).args(targets);
    match run_reference_replay_command(command, &binary, "exact_leanchecker", timeout)? {
        ReferenceCorpusVerdict::Accepted {
            duration,
            stdout,
            stderr,
        } => match validate_exact_completions(targets, &stdout) {
            Ok(()) => Ok(ReferenceCorpusVerdict::Accepted {
                duration,
                stdout,
                stderr,
            }),
            Err(reason) => Ok(ReferenceCorpusVerdict::NoAnswer {
                reason,
                duration,
                stdout,
                stderr,
            }),
        },
        other => Ok(other),
    }
}

#[test]
fn exact_module_completion_join_refuses_missing_duplicate_and_unexpected_rows() {
    let targets = ["Mathlib.A".to_string(), "Mathlib.B".to_string()];
    validate_exact_completions(
        &targets,
        "replayed exact module Mathlib.A\nreplayed exact module Mathlib.B\n",
    )
    .expect("accept the exact two-sided completion join");
    for mutant in [
        "replayed exact module Mathlib.A\n",
        "replayed exact module Mathlib.A\nreplayed exact module Mathlib.A\n",
        "replayed exact module Mathlib.A\nreplayed exact module Mathlib.C\n",
    ] {
        assert!(
            validate_exact_completions(&targets, mutant).is_err(),
            "completion mutant survived: {mutant:?}"
        );
    }
}

#[test]
#[ignore = "on-demand live process check against the SUITE.lock-pinned Reference"]
fn exact_module_driver_replays_one_real_pinned_module() {
    let reference_lib =
        reference_lib().expect("pinned Reference library required for the exact-driver probe");
    let targets = vec!["Init.Prelude".to_string()];
    match run_exact_leanchecker_with_search_roots(
        &reference_lib,
        &[reference_lib.as_path()],
        &targets,
        DEFAULT_LEANCHECKER_TIMEOUT,
    )
    .expect("launch exact-module Reference driver")
    {
        ReferenceCorpusVerdict::Accepted { stdout, stderr, .. } => {
            validate_exact_completions(&targets, &stdout)
                .expect("the live driver must prove exact completion");
            assert!(stderr.is_empty(), "live exact driver stderr: {stderr}");
        }
        other => panic!("live exact-module Reference replay did not accept: {other:?}"),
    }
}

fn run_leanchecker_batches_with_search_roots(
    reference_lib: &Path,
    search_roots: &[&Path],
    batches: Vec<LeancheckerBatch>,
    total_timeout: Duration,
    process_timeout: Duration,
    mut batch_accepted: impl FnMut(&LeancheckerBatch) -> Result<(), String>,
) -> Result<ReferenceCorpusVerdict, String> {
    if batches.len() == 1 {
        let batch = &batches[0];
        let verdict = match batch.mode {
            LeancheckerBatchMode::Prefix => run_leanchecker_with_search_roots(
                reference_lib,
                search_roots,
                &batch.targets,
                total_timeout.min(process_timeout),
            ),
            LeancheckerBatchMode::Exact => run_exact_leanchecker_with_search_roots(
                reference_lib,
                search_roots,
                &batch.targets,
                total_timeout.min(process_timeout),
            ),
        }?;
        if matches!(&verdict, ReferenceCorpusVerdict::Accepted { .. }) {
            batch_accepted(batch)?;
        }
        return Ok(verdict);
    }

    let started = Instant::now();
    let batch_count = batches.len();
    let mut accepted_stdout_bytes = 0_usize;
    let mut accepted_stderr_bytes = 0_usize;
    for (index, batch) in batches.iter().enumerate() {
        let remaining = total_timeout.saturating_sub(started.elapsed());
        if remaining.is_zero() {
            return Ok(ReferenceCorpusVerdict::NoAnswer {
                reason: format!(
                    "leanchecker batch plan exceeded {} seconds before batch {}/{}",
                    total_timeout.as_secs(),
                    index + 1,
                    batch_count
                ),
                duration: started.elapsed(),
                stdout: String::new(),
                stderr: String::new(),
            });
        }
        let verdict = match batch.mode {
            LeancheckerBatchMode::Prefix => run_leanchecker_with_search_roots(
                reference_lib,
                search_roots,
                &batch.targets,
                remaining.min(process_timeout),
            ),
            LeancheckerBatchMode::Exact => run_exact_leanchecker_with_search_roots(
                reference_lib,
                search_roots,
                &batch.targets,
                remaining.min(process_timeout),
            ),
        }?;
        match verdict {
            ReferenceCorpusVerdict::Accepted {
                duration,
                stdout,
                stderr,
            } => {
                batch_accepted(batch)?;
                accepted_stdout_bytes = accepted_stdout_bytes.saturating_add(stdout.len());
                accepted_stderr_bytes = accepted_stderr_bytes.saturating_add(stderr.len());
                eprintln!(
                    "kernel_reference_corpus oracle-batch: verdict=accepted batch={}/{} \
                     mode={} targets={} inventory_modules={} duration_ms={} stdout_bytes={} stderr_bytes={}",
                    index + 1,
                    batch_count,
                    batch.mode.label(),
                    batch.targets.len(),
                    batch.matched_modules,
                    duration.as_millis(),
                    stdout.len(),
                    stderr.len()
                );
            }
            ReferenceCorpusVerdict::Rejected {
                status,
                stdout,
                stderr,
                ..
            } => {
                return Ok(ReferenceCorpusVerdict::Rejected {
                    status,
                    duration: started.elapsed(),
                    stdout,
                    stderr,
                });
            }
            ReferenceCorpusVerdict::NoAnswer {
                reason,
                stdout,
                stderr,
                ..
            } => {
                return Ok(ReferenceCorpusVerdict::NoAnswer {
                    reason: format!(
                        "Reference replay batch {}/{} mode={} for targets {:?}: {reason}",
                        index + 1,
                        batch_count,
                        batch.mode.label(),
                        batch.targets.iter().take(8).collect::<Vec<_>>()
                    ),
                    duration: started.elapsed(),
                    stdout,
                    stderr,
                });
            }
        }
    }
    Ok(ReferenceCorpusVerdict::Accepted {
        duration: started.elapsed(),
        stdout: format!(
            "accepted {batch_count} deterministic leanchecker batches; \
             child_stdout_bytes={accepted_stdout_bytes}"
        ),
        stderr: if accepted_stderr_bytes == 0 {
            String::new()
        } else {
            format!("child_stderr_bytes={accepted_stderr_bytes}")
        },
    })
}

/// Bounded two-way cross-load evidence for the exact closure-free subset that
/// exists: the pinned Reference consumes fresh import-free v2/v3 modules with
/// one ordinary polymorphic definition, and our reader consumes a closure-free
/// v3 `ModuleData` emitted by the same verified pin. This does not by itself
/// establish FL-INV-04 byte identity. The output directory is operator-supplied
/// and retained so every oracle input can be inspected after the run; existing
/// paths are refused rather than overwritten.
#[ignore = "cost: invokes the pinned Reference kernel over freshly emitted olean modules"]
#[test]
fn closure_free_v2_and_v3_modules_cross_load_with_the_pin_and_reject_bad_semantics() {
    fn identity_definition(module: &str, well_typed: bool) -> ConstantInfo {
        let universe_name = Name::str(Name::anonymous(), "u");
        let alpha_name = Name::str(Name::anonymous(), "alpha");
        let value_name = Name::str(Name::anonymous(), "value");
        let declaration_name =
            Name::str(Name::str(Name::anonymous(), module), "polymorphicIdentity");
        let alpha_sort = Expr::sort(Level::param(universe_name.clone()));
        let identity_type = Expr::forall_e(
            alpha_name.clone(),
            alpha_sort.clone(),
            Expr::forall_e(
                value_name.clone(),
                Expr::bvar(0).expect("alpha binder"),
                Expr::bvar(1).expect("alpha result"),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let body = if well_typed {
            Expr::bvar(0).expect("identity value")
        } else {
            Expr::sort(Level::zero())
        };
        let identity_value = Expr::lam(
            alpha_name,
            alpha_sort,
            Expr::lam(
                value_name,
                Expr::bvar(0).expect("value binder type"),
                body,
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: declaration_name.clone(),
                level_params: vec![universe_name],
                type_: identity_type,
            },
            value: identity_value,
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![declaration_name],
        })
    }

    fn write_new(path: &Path, bytes: &[u8]) {
        let mut file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .unwrap_or_else(|error| panic!("create retained probe {}: {error}", path.display()));
        file.write_all(bytes)
            .unwrap_or_else(|error| panic!("write retained probe {}: {error}", path.display()));
        file.sync_all()
            .unwrap_or_else(|error| panic!("sync retained probe {}: {error}", path.display()));
    }

    let reference_lib = reference_lib().expect("pinned Reference stdlib required");
    let toolchain = reference_lib
        .parent()
        .and_then(Path::parent)
        .expect("Reference library belongs to a toolchain");
    let pinned_lean = toolchain.join("bin/lean");
    let version = Command::new(&pinned_lean)
        .env_clear()
        .arg("--version")
        .output()
        .unwrap_or_else(|error| panic!("run pinned lean {}: {error}", pinned_lean.display()));
    let version_text = String::from_utf8_lossy(&version.stdout);
    assert!(
        version.status.success() && version_text.contains(format::PIN_COMMIT),
        "Reference executable must match generated olean pin {}: {version_text}",
        format::PIN_COMMIT
    );
    let output_dir = PathBuf::from(
        std::env::var_os("FLN_OLEAN_REFERENCE_PROBE_DIR")
            .expect("FLN_OLEAN_REFERENCE_PROBE_DIR must name a new retained directory"),
    );
    fs::create_dir(&output_dir).unwrap_or_else(|error| {
        panic!(
            "create new retained probe directory {}: {error}",
            output_dir.display()
        )
    });

    let cases = [
        ("FlnWriterReferenceV2", 2, true),
        ("FlnWriterReferenceV2Bad", 2, false),
        ("FlnWriterReferenceV3", 3, true),
        ("FlnWriterReferenceV3Bad", 3, false),
    ];
    for (module, version, well_typed) in cases {
        let definition = identity_definition(module, well_typed);
        let encoded = encode_module(
            ModuleWriteInput {
                is_module: false,
                imports: &[],
                constants: &[definition],
                extra_const_names: &[],
            },
            OleanWriteHeader {
                version,
                flags: 1,
                lean_version: format::PIN_TAG
                    .strip_prefix('v')
                    .expect("generated pin tag starts with v"),
                githash: format::PIN_COMMIT,
                base_addr: 0x2f00_0000_0000,
            },
            WriteBudget::default(),
        )
        .expect("fresh module encoding");
        let view = OleanView::parse(&encoded.bytes).expect("fresh module framing");
        assert_eq!(view.header.version, version);
        view.shared_audit().expect("fresh module region audit");
        write_new(&output_dir.join(format!("{module}.olean")), &encoded.bytes);
    }

    let search_roots = [output_dir.as_path(), reference_lib.as_path()];
    for module in ["FlnWriterReferenceV2", "FlnWriterReferenceV3"] {
        match run_leanchecker_with_search_roots(
            &reference_lib,
            &search_roots,
            &[module.to_owned()],
            DEFAULT_LEANCHECKER_TIMEOUT,
        )
        .expect("run pinned Reference over fresh good module")
        {
            ReferenceCorpusVerdict::Accepted { stdout, stderr, .. } => {
                assert!(stdout.contains(&format!("replaying {module}")));
                assert!(stderr.is_empty(), "accepted module wrote stderr: {stderr}");
            }
            verdict => panic!("pinned Reference did not accept fresh {module}: {verdict:?}"),
        }
    }
    for module in ["FlnWriterReferenceV2Bad", "FlnWriterReferenceV3Bad"] {
        match run_leanchecker_with_search_roots(
            &reference_lib,
            &search_roots,
            &[module.to_owned()],
            DEFAULT_LEANCHECKER_TIMEOUT,
        )
        .expect("run pinned Reference over fresh ill-typed module")
        {
            ReferenceCorpusVerdict::Rejected { stderr, .. } => {
                assert!(stderr.contains("(kernel) declaration type mismatch"));
                assert!(stderr.contains(&format!("{module}.polymorphicIdentity")));
            }
            verdict => panic!("pinned Reference did not reject fresh {module}: {verdict:?}"),
        }
    }

    let producer_source = output_dir.join("FlnReferenceV3Producer.lean");
    let reference_v3 = output_dir.join("FlnReferenceProducedV3.olean");
    write_new(
        &producer_source,
        br#"import Lean.Environment
import Lean.CompactedRegion

unsafe def main (args : List String) : IO UInt32 := do
  let some path := args.head? | return 2
  let data : Lean.ModuleData := {
    isModule := false
    imports := #[]
    constNames := #[]
    constants := #[]
    extraConstNames := #[`Fln.Reference.V3]
    entries := #[]
  }
  let _ <- Lean.CompactedRegion.save path `FlnReferenceProducedV3 data #[] none true
  return 0
"#,
    );
    let produced = Command::new(&pinned_lean)
        .env_clear()
        .arg("--run")
        .arg(&producer_source)
        .arg(&reference_v3)
        .output()
        .expect("run pinned Reference v3 producer");
    assert!(
        produced.status.success(),
        "pinned Reference v3 producer failed: stdout={} stderr={}",
        String::from_utf8_lossy(&produced.stdout),
        String::from_utf8_lossy(&produced.stderr)
    );
    assert!(produced.stdout.is_empty());
    assert!(produced.stderr.is_empty());
    let reference_bytes = fs::read(&reference_v3).expect("read Reference-produced v3 module");
    let view = OleanView::parse(&reference_bytes).expect("parse Reference-produced v3 module");
    assert_eq!(view.header.version, 3);
    let audit = view
        .shared_audit()
        .expect("audit Reference-produced v3 module");
    assert!(audit.objects > 0);
    let module = view
        .module_data(WalkBudget::default())
        .expect("decode Reference-produced v3 ModuleData");
    assert!(!module.is_module);
    assert!(module.imports.is_empty());
    assert_eq!(module.constants, 0);
    assert_eq!(module.extra_const_names, 1);
}

fn prefix_oracle_hash(reference_lib: &Path) -> Result<String, String> {
    let path = leanchecker_path(reference_lib)?;
    let checker_bytes =
        fs::read(&path).map_err(|error| format!("read oracle {}: {error}", path.display()))?;
    let lean_path = path
        .parent()
        .ok_or_else(|| format!("leanchecker {} has no bin directory", path.display()))?
        .join("lean");
    let lean_bytes = fs::read(&lean_path)
        .map_err(|error| format!("read oracle helper {}: {error}", lean_path.display()))?;
    Ok(tagged_fixture_hash(
        b"fln.kernel-reference-corpus.oracle/1",
        &[&checker_bytes, &lean_bytes],
    ))
}

fn exact_oracle_hash(reference_lib: &Path) -> Result<String, String> {
    let lean_path = reference_lean_path(reference_lib)?;
    let lean_bytes = fs::read(&lean_path)
        .map_err(|error| format!("read exact oracle {}: {error}", lean_path.display()))?;
    let driver_path = exact_leanchecker_driver_path()?;
    let driver_bytes = fs::read(&driver_path).map_err(|error| {
        format!(
            "read exact oracle driver {}: {error}",
            driver_path.display()
        )
    })?;
    Ok(tagged_fixture_hash(
        b"fln.kernel-reference-corpus.exact-oracle/1",
        &[&lean_bytes, &driver_bytes],
    ))
}

struct ReferenceOracleHashes {
    prefix: String,
    exact: String,
}

impl ReferenceOracleHashes {
    fn for_batch(&self, mode: LeancheckerBatchMode) -> &str {
        match mode {
            LeancheckerBatchMode::Prefix => &self.prefix,
            LeancheckerBatchMode::Exact => &self.exact,
        }
    }
}

fn checkpoint_content(module: &CorpusModule, oracle_hash: &str) -> String {
    format!(
        "schema=fln.kernel-reference-corpus.checkpoint/1\n\
         module={}\n\
         olean_hash={}\n\
         oracle_hash={oracle_hash}\n\
         verdict=accepted\n\
         complete=true\n",
        module.name, module.olean_hash
    )
}

fn checkpoint_path(dir: &Path, module: &CorpusModule, oracle_hash: &str) -> PathBuf {
    let key = tagged_fixture_hash(
        b"fln.kernel-reference-corpus.checkpoint-key/1",
        &[
            module.name.as_bytes(),
            module.olean_hash.as_bytes(),
            oracle_hash.as_bytes(),
        ],
    );
    dir.join(format!("{key}.record"))
}

fn checkpoint_is_complete(
    dir: &Path,
    module: &CorpusModule,
    oracle_hash: &str,
) -> Result<bool, String> {
    let path = checkpoint_path(dir, module, oracle_hash);
    match fs::read_to_string(&path) {
        Ok(actual) => {
            let expected = checkpoint_content(module, oracle_hash);
            if actual != expected {
                return Err(format!(
                    "checkpoint {} exists but is not the exact complete record for {}",
                    path.display(),
                    module.name
                ));
            }
            Ok(true)
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(format!("read checkpoint {}: {error}", path.display())),
    }
}

fn checkpoint_is_complete_under_either_oracle(
    dir: &Path,
    module: &CorpusModule,
    hashes: &ReferenceOracleHashes,
) -> Result<bool, String> {
    if checkpoint_is_complete(dir, module, &hashes.prefix)? {
        return Ok(true);
    }
    checkpoint_is_complete(dir, module, &hashes.exact)
}

fn persist_checkpoint(dir: &Path, module: &CorpusModule, oracle_hash: &str) -> Result<(), String> {
    if let Ok(metadata) = fs::symlink_metadata(dir)
        && metadata.file_type().is_symlink()
    {
        return Err(format!(
            "checkpoint directory {} must not be a symlink",
            dir.display()
        ));
    }
    fs::create_dir_all(dir)
        .map_err(|error| format!("create checkpoint directory {}: {error}", dir.display()))?;
    let path = checkpoint_path(dir, module, oracle_hash);
    let expected = checkpoint_content(module, oracle_hash);
    match fln::publish_file_atomic_new(expected.as_bytes(), &path) {
        Ok(()) => Ok(()),
        Err(error) if error.primary_io_error_kind() == Some(std::io::ErrorKind::AlreadyExists) => {
            checkpoint_is_complete(dir, module, oracle_hash).and_then(|complete| {
                complete.then_some(()).ok_or_else(|| {
                    format!(
                        "concurrent checkpoint publication did not complete {}",
                        path.display()
                    )
                })
            })
        }
        Err(error) => Err(format!("publish checkpoint {}: {error}", path.display())),
    }
}

fn reference_verdict_with_resume(
    reference_lib: &Path,
    search_roots: &[&Path],
    inventory: &CorpusInventory,
    total_timeout: Duration,
    process_timeout: Duration,
    max_modules_per_process: usize,
) -> Result<(ReferenceCorpusVerdict, &'static str), String> {
    let oracle_hashes = ReferenceOracleHashes {
        prefix: prefix_oracle_hash(reference_lib)?,
        exact: exact_oracle_hash(reference_lib)?,
    };
    let checkpoint_dir = std::env::var_os("FLN_CORPUS_CHECKPOINT_DIR").map(PathBuf::from);
    let mut completed_modules = BTreeSet::new();
    if let Some(dir) = &checkpoint_dir {
        let mut expected = 0_u64;
        for module in inventory
            .modules
            .values()
            .filter(|module| module.decoded != 0)
        {
            expected += 1;
            if checkpoint_is_complete_under_either_oracle(dir, module, &oracle_hashes)? {
                completed_modules.insert(module.name.clone());
            }
        }
        if expected != 0 && completed_modules.len() as u64 == expected {
            return Ok((
                ReferenceCorpusVerdict::Accepted {
                    duration: Duration::ZERO,
                    stdout: format!(
                        "resumed {} immutable per-module oracle records from {}",
                        completed_modules.len(),
                        dir.display()
                    ),
                    stderr: String::new(),
                },
                "checkpoint",
            ));
        }
    }
    let required_modules = inventory
        .modules
        .values()
        .filter(|module| module.decoded != 0 && !completed_modules.contains(&module.name))
        .map(|module| module.name.as_str())
        .collect::<Vec<_>>();
    let resumed = !completed_modules.is_empty();
    let batches =
        leanchecker_batches_for_required(inventory, &required_modules, max_modules_per_process)?;
    let verdict = run_leanchecker_batches_with_search_roots(
        reference_lib,
        search_roots,
        batches,
        total_timeout,
        process_timeout,
        |batch| {
            let Some(dir) = &checkpoint_dir else {
                return Ok(());
            };
            let oracle_hash = oracle_hashes.for_batch(batch.mode);
            for module in inventory
                .modules
                .values()
                .filter(|module| module.decoded != 0 && batch.covers_module(&module.name))
            {
                persist_checkpoint(dir, module, oracle_hash)?;
            }
            Ok(())
        },
    )?;
    if matches!(verdict, ReferenceCorpusVerdict::Accepted { .. })
        && let Some(dir) = &checkpoint_dir
    {
        for module in inventory
            .modules
            .values()
            .filter(|module| module.decoded != 0)
        {
            if !checkpoint_is_complete_under_either_oracle(dir, module, &oracle_hashes)? {
                return Err(format!(
                    "accepted Reference replay left no complete checkpoint for {}",
                    module.name
                ));
            }
        }
    }
    Ok((verdict, if resumed { "live+checkpoint" } else { "live" }))
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CorpusAxisVerdict {
    Accepted,
    Rejected(String),
    NoAnswer(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CorpusDivergence {
    Agree,
    UnsoundlyPermissive { oracle: String },
    Restrictive { ours: String },
    NoAnswer { detail: String },
}

fn classify_corpus_verdict(
    oracle: &CorpusAxisVerdict,
    ours: &CorpusAxisVerdict,
) -> CorpusDivergence {
    match (oracle, ours) {
        (CorpusAxisVerdict::NoAnswer(detail), _) => CorpusDivergence::NoAnswer {
            detail: format!("oracle: {detail}"),
        },
        (_, CorpusAxisVerdict::NoAnswer(detail)) => CorpusDivergence::NoAnswer {
            detail: format!("subject: {detail}"),
        },
        (CorpusAxisVerdict::Accepted, CorpusAxisVerdict::Accepted)
        | (CorpusAxisVerdict::Rejected(_), CorpusAxisVerdict::Rejected(_)) => {
            CorpusDivergence::Agree
        }
        (CorpusAxisVerdict::Rejected(oracle), CorpusAxisVerdict::Accepted) => {
            CorpusDivergence::UnsoundlyPermissive {
                oracle: oracle.clone(),
            }
        }
        (CorpusAxisVerdict::Accepted, CorpusAxisVerdict::Rejected(ours)) => {
            CorpusDivergence::Restrictive { ours: ours.clone() }
        }
    }
}

struct CorpusCarveOut {
    declaration: &'static str,
    justification: &'static str,
}

/// D23 applies only to the restrictive direction. This registry is
/// intentionally empty: every future row is a public Behavior Note, not a
/// suppression, and must name one decoded declaration plus its justification.
const CORPUS_CARVE_OUTS: &[CorpusCarveOut] = &[];

fn corpus_carve_out(name: &str) -> Option<&'static CorpusCarveOut> {
    CORPUS_CARVE_OUTS.iter().find(|row| row.declaration == name)
}

fn subject_axis(outcome: &UnitOutcome) -> CorpusAxisVerdict {
    if outcome.outcome == "accepted" {
        CorpusAxisVerdict::Accepted
    } else if outcome.outcome.starts_with("rejected:") {
        CorpusAxisVerdict::Rejected(format!("{}: {}", outcome.outcome, outcome.message))
    } else {
        CorpusAxisVerdict::NoAnswer(format!("{}: {}", outcome.outcome, outcome.message))
    }
}

#[derive(Debug, Default)]
struct CorpusCounts {
    decoded: u64,
    compared: u64,
    agree: u64,
    unsoundly_permissive: u64,
    restrictive_with_carve_out: u64,
    restrictive_without_carve_out: u64,
    unscorable: u64,
    oracle_skipped: u64,
    subject_no_answer: u64,
}

impl CorpusCounts {
    fn disagreements(&self) -> u64 {
        self.unsoundly_permissive
            + self.restrictive_with_carve_out
            + self.restrictive_without_carve_out
    }

    fn add(&mut self, other: &CorpusCounts) {
        self.decoded += other.decoded;
        self.compared += other.compared;
        self.agree += other.agree;
        self.unsoundly_permissive += other.unsoundly_permissive;
        self.restrictive_with_carve_out += other.restrictive_with_carve_out;
        self.restrictive_without_carve_out += other.restrictive_without_carve_out;
        self.unscorable += other.unscorable;
        self.oracle_skipped += other.oracle_skipped;
        self.subject_no_answer += other.subject_no_answer;
    }

    fn assert_conservation(&self, scope: &str) {
        assert_eq!(
            self.decoded,
            self.compared + self.unscorable,
            "{scope}: decoded must equal compared + unscorable"
        );
        assert_eq!(
            self.compared,
            self.agree
                + self.unsoundly_permissive
                + self.restrictive_with_carve_out
                + self.restrictive_without_carve_out,
            "{scope}: compared rows must conserve the D23 direction buckets"
        );
    }
}

/// Tribunal-only adapter for the Reference's `finalizeImport` duplicate law.
///
/// FrankenLean's authoritative [`Environment`] remains a one-name map and is
/// never overwritten. The shadow map records only the richer Reference
/// representative chosen by `subsumesInfo`; every such replacement has the
/// same name, type, level parameters, and kernel safety, so the original
/// declaration in `environment` is observationally equivalent for kernel
/// checking. Keeping the representative separately is still necessary:
/// subsequent duplicate decisions inspect whether the Reference retained a
/// theorem or an axiom.
#[derive(Clone, Default)]
struct ReferenceFixtureContext {
    environment: Environment,
    representative_overrides: BTreeMap<Name, ConstantInfo>,
}

impl ReferenceFixtureContext {
    fn new() -> Self {
        Self::default()
    }

    fn representative(&self, name: &Name) -> Option<&ConstantInfo> {
        self.representative_overrides
            .get(name)
            .or_else(|| self.environment.find(name))
    }

    fn set_representative(&mut self, info: &ConstantInfo) {
        let name = info.name();
        if self.environment.find(name) == Some(info) {
            self.representative_overrides.remove(name);
        } else {
            self.representative_overrides
                .insert(name.clone(), info.clone());
        }
    }
}

/// The pin's deliberately cheap proposition recognizer used only by
/// `finalizeImport.subsumesInfo` for axiom/axiom extended duplicates.
fn reference_import_is_prop_cheap(context: &ReferenceFixtureContext, type_: &Expr) -> bool {
    let mut result = type_.clone();
    while let ExprNode::ForallE { body, .. } = result.node() {
        result = body.clone();
    }

    let mut head = result;
    let mut argument_count = 0_usize;
    while let ExprNode::App { f, .. } = head.node() {
        let Some(next_count) = argument_count.checked_add(1) else {
            return false;
        };
        argument_count = next_count;
        head = f.clone();
    }
    let ExprNode::Const { name, .. } = head.node() else {
        return false;
    };
    let Some(predicate) = context.representative(name) else {
        return false;
    };
    let mut predicate_type = predicate.constant_val().type_.clone();
    for _ in 0..argument_count {
        let ExprNode::ForallE { body, .. } = predicate_type.node() else {
            return false;
        };
        predicate_type = body.clone();
    }
    matches!(
        predicate_type.node(),
        ExprNode::Sort { level } if level.is_zero()
    )
}

/// Exact port of the three `subsumesInfo` arms in the pinned
/// `Lean.Environment.finalizeImport`.
fn reference_import_subsumes(
    context: &ReferenceFixtureContext,
    richer: &ConstantInfo,
    weaker: &ConstantInfo,
) -> bool {
    let richer_base = richer.constant_val();
    let weaker_base = weaker.constant_val();
    if richer_base.name != weaker_base.name
        || richer_base.type_ != weaker_base.type_
        || richer_base.level_params != weaker_base.level_params
    {
        return false;
    }
    match (richer, weaker) {
        (ConstantInfo::Thm(richer), ConstantInfo::Thm(weaker)) => richer.all == weaker.all,
        (ConstantInfo::Thm(richer), ConstantInfo::Axiom(weaker)) => {
            richer.all.as_slice() == std::slice::from_ref(&weaker.base.name) && !weaker.is_unsafe
        }
        (ConstantInfo::Axiom(richer), ConstantInfo::Axiom(weaker)) => {
            richer.is_unsafe == weaker.is_unsafe
                && reference_import_is_prop_cheap(context, &richer.base.type_)
        }
        _ => false,
    }
}

#[derive(Debug, Default)]
struct ReferenceFixtureMerge {
    collisions: Vec<String>,
    extended_duplicates: u64,
    extended_only_duplicates: u64,
}

fn extend_reference_fixture_environment(
    mut context: ReferenceFixtureContext,
    infos: &[ConstantInfo],
    module: &str,
) -> Result<(ReferenceFixtureContext, ReferenceFixtureMerge), String> {
    let mut report = ReferenceFixtureMerge::default();
    for info in infos {
        if let Some(existing) = context.representative(info.name()).cloned() {
            let legacy_duplicate = reference_replay_duplicate(&existing, info);
            if reference_import_subsumes(&context, info, &existing) {
                context.set_representative(info);
                report.extended_duplicates += 1;
                report.extended_only_duplicates += u64::from(!legacy_duplicate);
            } else if reference_import_subsumes(&context, &existing, info) {
                report.extended_duplicates += 1;
                report.extended_only_duplicates += u64::from(!legacy_duplicate);
            } else {
                report.collisions.push(info.name().to_display_string());
            }
            continue;
        }
        context.environment = context
            .environment
            .add_decl(info.clone())
            .map_err(|error| {
                format!(
                    "publish decoded fixture declaration {} from {module}: {error:?}",
                    info.name().to_display_string()
                )
            })?;
    }
    Ok((context, report))
}

/// Lean.Replay's exact duplicate-theorem exception: proof values may differ,
/// but name, statement, universe parameters, and mutual-block membership must
/// agree. Such a second row is not submitted to the Reference kernel.
fn reference_replay_duplicate(existing: &ConstantInfo, candidate: &ConstantInfo) -> bool {
    let (ConstantInfo::Thm(existing), ConstantInfo::Thm(candidate)) = (existing, candidate) else {
        return false;
    };
    existing.base.name == candidate.base.name
        && existing.base.type_ == candidate.base.type_
        && existing.base.level_params == candidate.base.level_params
        && existing.all == candidate.all
}

/// Leanchecker first folds the serialized `(constNames, constants)` arrays
/// into a `HashMap`, so a repeated name contributes exactly its last row.
/// Earlier serialized rows are decoded-corpus rows but receive no oracle
/// verdict; preserve their original indices so the census cannot lose them.
fn reference_active_rows(
    infos: &[ConstantInfo],
) -> (Vec<ConstantInfo>, Vec<usize>, HashSet<usize>) {
    let mut last = HashMap::<Name, usize>::new();
    for (index, info) in infos.iter().enumerate() {
        last.insert(info.name().clone(), index);
    }
    let mut active = Vec::new();
    let mut active_to_decoded = Vec::new();
    let mut shadowed = HashSet::new();
    for (index, info) in infos.iter().enumerate() {
        if last[info.name()] == index {
            active.push(info.clone());
            active_to_decoded.push(index);
        } else {
            shadowed.insert(index);
        }
    }
    (active, active_to_decoded, shadowed)
}

fn score_accepted_reference_module(
    module: &CorpusModule,
    decoded_infos: &[ConstantInfo],
    active_infos: &[ConstantInfo],
    active_to_decoded: &[usize],
    shadowed: &HashSet<usize>,
    prep: &PreparedReplay,
    run: &MatrixRun,
) -> CorpusCounts {
    assert_eq!(
        prep.items.len(),
        run.outcomes.len(),
        "{}: every prepared unit has an outcome",
        module.name
    );
    let context_unscorable = prep
        .context_unscorable
        .iter()
        .map(|(index, _, reason)| (active_to_decoded[*index], *reason))
        .collect::<HashMap<_, _>>();
    let mut represented = HashSet::new();
    let mut counts = CorpusCounts {
        decoded: module.decoded,
        oracle_skipped: module.oracle_skipped,
        unscorable: module.oracle_skipped,
        ..CorpusCounts::default()
    };
    for (item, outcome) in prep.items.iter().zip(&run.outcomes) {
        let mut applicable_members = Vec::new();
        for (member_index, name) in item.member_indices.iter().zip(&item.member_names) {
            let decoded_index = active_to_decoded[*member_index];
            assert!(
                represented.insert(decoded_index),
                "{}: declaration row {} ({}) appears in two admission units",
                module.name,
                decoded_index,
                name.to_display_string()
            );
            let info = &active_infos[*member_index];
            if !reference_replay_skips(info) {
                applicable_members.push(name);
            }
        }
        if applicable_members.is_empty() {
            continue;
        }
        let ours = subject_axis(outcome);
        let divergence = classify_corpus_verdict(&CorpusAxisVerdict::Accepted, &ours);
        match divergence {
            CorpusDivergence::Agree => {
                counts.agree += applicable_members.len() as u64;
                counts.compared += applicable_members.len() as u64;
            }
            CorpusDivergence::UnsoundlyPermissive { .. } => {
                unreachable!("Reference accepted this module")
            }
            CorpusDivergence::Restrictive { ours } => {
                for name in applicable_members {
                    let rendered = name.to_display_string();
                    counts.compared += 1;
                    if let Some(row) = corpus_carve_out(&rendered) {
                        assert!(
                            !row.justification.trim().is_empty(),
                            "carve-out {rendered} has no justification"
                        );
                        counts.restrictive_with_carve_out += 1;
                        eprintln!(
                            "kernel_reference_corpus finding: module={} declaration={} \
                             direction=restrictive carve_out=true ours={} justification={}",
                            module.name, rendered, ours, row.justification
                        );
                    } else {
                        counts.restrictive_without_carve_out += 1;
                        eprintln!(
                            "kernel_reference_corpus finding: module={} declaration={} \
                             direction=restrictive carve_out=false ours={}",
                            module.name, rendered, ours
                        );
                    }
                }
            }
            CorpusDivergence::NoAnswer { detail } => {
                let affected = applicable_members.len() as u64;
                counts.unscorable += affected;
                counts.subject_no_answer += affected;
                eprintln!(
                    "kernel_reference_corpus finding: module={} declaration={} \
                     direction=unscorable affected={} detail={}",
                    module.name,
                    item.lead.to_display_string(),
                    affected,
                    detail
                );
            }
        }
    }
    let mut oracle_omitted = Vec::new();
    let mut subject_omitted = Vec::new();
    for (index, info) in decoded_infos.iter().enumerate() {
        if !reference_replay_skips(info) && !represented.contains(&index) {
            let rendered = info.name().to_display_string();
            if shadowed.contains(&index) {
                oracle_omitted.push((rendered, "reference_hash_map_shadowed_row"));
            } else if let Some(reason) = context_unscorable.get(&index) {
                if *reason == "reference_replay_duplicate_theorem" {
                    oracle_omitted.push((rendered, *reason));
                } else {
                    subject_omitted.push(rendered);
                }
            } else {
                subject_omitted.push(rendered);
            }
        }
    }
    if !oracle_omitted.is_empty() {
        counts.unscorable += oracle_omitted.len() as u64;
        counts.oracle_skipped += oracle_omitted.len() as u64;
        eprintln!(
            "kernel_reference_corpus finding: module={} direction=unscorable \
             reason=reference_context_skip affected={} first={:?}",
            module.name,
            oracle_omitted.len(),
            oracle_omitted.iter().take(5).collect::<Vec<_>>()
        );
    }
    if !subject_omitted.is_empty() {
        counts.unscorable += subject_omitted.len() as u64;
        counts.subject_no_answer += subject_omitted.len() as u64;
        eprintln!(
            "kernel_reference_corpus finding: module={} direction=unscorable \
             reason=subject_has_no_declaration_envelope affected={} first={:?}",
            module.name,
            subject_omitted.len(),
            subject_omitted.iter().take(5).collect::<Vec<_>>()
        );
    }
    counts.assert_conservation(&module.name);
    counts
}

#[test]
fn corpus_comparator_preserves_d23_asymmetry_and_no_answer() {
    use CorpusAxisVerdict::{Accepted, NoAnswer, Rejected};

    assert_eq!(
        classify_corpus_verdict(&Accepted, &Accepted),
        CorpusDivergence::Agree
    );
    assert_eq!(
        classify_corpus_verdict(&Rejected("reference".into()), &Rejected("ours".into())),
        CorpusDivergence::Agree
    );
    assert!(matches!(
        classify_corpus_verdict(&Rejected("reference".into()), &Accepted),
        CorpusDivergence::UnsoundlyPermissive { .. }
    ));
    assert!(matches!(
        classify_corpus_verdict(&Accepted, &Rejected("ours".into())),
        CorpusDivergence::Restrictive { .. }
    ));
    assert!(matches!(
        classify_corpus_verdict(&NoAnswer("oracle crash".into()), &Accepted),
        CorpusDivergence::NoAnswer { .. }
    ));
    assert!(matches!(
        classify_corpus_verdict(&Accepted, &NoAnswer("subject exhausted".into())),
        CorpusDivergence::NoAnswer { .. }
    ));
    assert!(
        CORPUS_CARVE_OUTS
            .iter()
            .all(|row| !row.justification.trim().is_empty()),
        "every D23 carve-out is explicit and justified"
    );
}

#[test]
fn reference_import_adapter_preserves_one_name_authority_and_rejects_conflicts() {
    use fln_env::constants::{AxiomVal, ConstantVal, TheoremVal};

    let name = Name::str(Name::anonymous(), "extendedDuplicate");
    let proposition = Expr::sort(fln_core::level::Level::zero());
    let base = ConstantVal {
        name: name.clone(),
        level_params: Vec::new(),
        type_: proposition.clone(),
    };
    let exported_axiom = ConstantInfo::Axiom(AxiomVal {
        base: base.clone(),
        is_unsafe: false,
    });
    let private_theorem = ConstantInfo::Thm(TheoremVal {
        base: base.clone(),
        value: proposition,
        all: vec![name.clone()],
    });

    let (context, seed) = extend_reference_fixture_environment(
        ReferenceFixtureContext::new(),
        std::slice::from_ref(&exported_axiom),
        "Exported",
    )
    .expect("seed fixture context");
    assert!(seed.collisions.is_empty());
    assert_eq!(seed.extended_duplicates, 0);
    assert_eq!(seed.extended_only_duplicates, 0);
    assert_eq!(context.environment.len(), 1);

    // The authoritative environment still refuses the duplicate. Only the
    // Tribunal adapter applies the Reference import law.
    assert!(
        context
            .environment
            .add_decl(private_theorem.clone())
            .is_err(),
        "extended duplicate handling must not weaken Environment::add_decl"
    );

    let (context, richer) = extend_reference_fixture_environment(
        context,
        std::slice::from_ref(&private_theorem),
        "Private",
    )
    .expect("merge richer theorem representation");
    assert!(richer.collisions.is_empty());
    assert_eq!(richer.extended_duplicates, 1);
    assert_eq!(richer.extended_only_duplicates, 1);
    assert_eq!(context.environment.len(), 1);
    assert!(matches!(
        context.environment.find(&name),
        Some(ConstantInfo::Axiom(_))
    ));
    assert!(matches!(
        context.representative(&name),
        Some(ConstantInfo::Thm(_))
    ));

    let replay = prepare_replay_from(
        context.environment.clone(),
        Some(&context),
        std::slice::from_ref(&private_theorem),
        false,
    );
    assert!(replay.items.is_empty());
    assert_eq!(
        replay.context_unscorable,
        vec![(0, name.clone(), "reference_replay_duplicate_theorem")],
        "the shadow representative must recover the Reference replay skip"
    );

    // The shadow representative is load-bearing: a later exported axiom is
    // subsumed by the retained theorem even though the one-name environment
    // itself still contains the first axiom.
    let (context, later) = extend_reference_fixture_environment(
        context,
        std::slice::from_ref(&exported_axiom),
        "LaterExport",
    )
    .expect("merge later weakened representation");
    assert!(later.collisions.is_empty());
    assert_eq!(later.extended_duplicates, 1);
    assert_eq!(later.extended_only_duplicates, 1);
    assert!(matches!(
        context.representative(&name),
        Some(ConstantInfo::Thm(_))
    ));

    let conflicting = ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: name.clone(),
            level_params: Vec::new(),
            type_: Expr::const_(Name::str(Name::anonymous(), "Different"), Vec::new()),
        },
        is_unsafe: false,
    });
    let (context, conflict) = extend_reference_fixture_environment(
        context,
        std::slice::from_ref(&conflicting),
        "Conflict",
    )
    .expect("classify conflicting duplicate");
    assert_eq!(
        conflict.collisions,
        vec![name.to_display_string()],
        "a type mismatch is a real collision, never an extended duplicate"
    );
    assert_eq!(conflict.extended_duplicates, 0);
    assert_eq!(conflict.extended_only_duplicates, 0);
    assert_eq!(context.environment.len(), 1);
    assert!(matches!(
        context.representative(&name),
        Some(ConstantInfo::Thm(_))
    ));

    let predicate_name = Name::str(Name::anonymous(), "Predicate");
    let predicate = ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: predicate_name.clone(),
            level_params: Vec::new(),
            type_: Expr::forall_e(
                Name::anonymous(),
                Expr::sort(fln_core::level::Level::zero()),
                Expr::sort(fln_core::level::Level::zero()),
                BinderInfo::Default,
            ),
        },
        is_unsafe: false,
    });
    let proposition_axiom_name = Name::str(Name::anonymous(), "propositionAxiom");
    let proposition_axiom = ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: proposition_axiom_name.clone(),
            level_params: Vec::new(),
            type_: Expr::app(
                Expr::const_(predicate_name, Vec::new()),
                Expr::sort(fln_core::level::Level::zero()),
            ),
        },
        is_unsafe: false,
    });
    let (axiom_context, _) = extend_reference_fixture_environment(
        ReferenceFixtureContext::new(),
        &[predicate, proposition_axiom.clone()],
        "AxiomSeed",
    )
    .expect("seed proposition-shaped axiom context");
    let (_, axiom_duplicate) = extend_reference_fixture_environment(
        axiom_context,
        std::slice::from_ref(&proposition_axiom),
        "AxiomDuplicate",
    )
    .expect("classify proposition-shaped axiom duplicate");
    assert!(axiom_duplicate.collisions.is_empty());
    assert_eq!(axiom_duplicate.extended_only_duplicates, 1);

    let type_predicate_name = Name::str(Name::anonymous(), "TypePredicate");
    let type_predicate = ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: type_predicate_name.clone(),
            level_params: Vec::new(),
            type_: Expr::forall_e(
                Name::anonymous(),
                Expr::sort(fln_core::level::Level::zero()),
                Expr::sort(
                    fln_core::level::Level::zero()
                        .succ()
                        .expect("the first successor level is representable"),
                ),
                BinderInfo::Default,
            ),
        },
        is_unsafe: false,
    });
    let type_axiom_name = Name::str(Name::anonymous(), "typeAxiom");
    let type_axiom = ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: type_axiom_name.clone(),
            level_params: Vec::new(),
            type_: Expr::app(
                Expr::const_(type_predicate_name, Vec::new()),
                Expr::sort(fln_core::level::Level::zero()),
            ),
        },
        is_unsafe: false,
    });
    let (type_context, _) = extend_reference_fixture_environment(
        ReferenceFixtureContext::new(),
        &[type_predicate, type_axiom.clone()],
        "TypeAxiomSeed",
    )
    .expect("seed non-proposition axiom context");
    let (_, type_duplicate) = extend_reference_fixture_environment(
        type_context,
        std::slice::from_ref(&type_axiom),
        "TypeAxiomDuplicate",
    )
    .expect("classify non-proposition axiom duplicate");
    assert_eq!(
        type_duplicate.collisions,
        vec![type_axiom_name.to_display_string()],
        "even an identical axiom duplicate is a conflict when isPropCheap is false"
    );
    assert_eq!(type_duplicate.extended_only_duplicates, 0);
}

#[test]
fn module_system_private_part_restores_bodies_and_private_auxiliaries() {
    let Some(reference_lib) = reference_lib() else {
        return;
    };
    let module = reference_lib.join("Init/Data/List/ToArrayImpl.olean");

    let public = fs::read(&module).expect("read public module part");
    let server = fs::read(module.with_extension("olean.server")).expect("read server module part");
    let private =
        fs::read(module.with_extension("olean.private")).expect("read private module part");

    let public_view = OleanView::parse(&public).expect("parse public module part");
    let public_infos = DeclDecoder::new(&public_view, WalkBudget::default())
        .decode_module_constants()
        .expect("decode public module part");
    assert_eq!(public_infos.len(), 5, "pin's public declaration census");

    let total_bytes = public.len() + server.len() + private.len();
    let decoded = fln::decode_olean_module_artifacts(
        &public,
        &server,
        &private,
        fln::OleanDecodeLimits::new(total_bytes),
    )
    .expect("decode the complete module chain through the product facade");
    assert!(decoded.companion_parts_loaded);
    let private_infos = decoded.constants;
    assert!(matches!(
        fln::decode_olean_module_artifacts(
            &public,
            &server,
            &private,
            fln::OleanDecodeLimits::new(total_bytes - 1),
        ),
        Err(fln::OleanDecodeError::ArtifactTooLarge {
            bytes,
            limit
        }) if bytes == total_bytes && limit == total_bytes - 1
    ));
    let mut wrong_server = server.clone();
    wrong_server[40] ^= 1;
    assert!(matches!(
        fln::decode_olean_module_artifacts(
            &public,
            &wrong_server,
            &private,
            fln::OleanDecodeLimits::new(total_bytes),
        ),
        Err(fln::OleanDecodeError::CompanionHeaderMismatch {
            part: fln::OleanCompanionPart::Server,
        })
    ));
    assert!(
        private_infos.len() > public_infos.len(),
        "private level must restore declarations absent from the exported part"
    );
    assert!(
        private_infos.iter().any(|info| {
            info.name().to_display_string()
                == "_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1"
        }),
        "equation compiler auxiliary omitted by public-only decode"
    );
    assert!(
        matches!(
            private_infos
                .iter()
                .find(|info| info.name().to_display_string() == "List.toArrayAux"),
            Some(ConstantInfo::Defn(_))
        ),
        "private level must retain the definition body rather than a weakened axiom"
    );

    let cli = fln_cli::run([
        std::ffi::OsString::from("check-olean"),
        std::ffi::OsString::from("--json"),
        module.clone().into_os_string(),
    ]);
    assert_eq!(cli.exit_code, 1, "{}", cli.stderr);
    assert!(
        cli.stderr.contains("\"class\":\"unresolved-imports\""),
        "the product path must load companions before it reaches the expected standalone import refusal: {}",
        cli.stderr
    );
    assert!(!cli.stderr.contains("missing .olean"));

    let directory = module
        .parent()
        .expect("real module has a library directory")
        .to_path_buf();
    let directory_cli = fln_cli::run([
        std::ffi::OsString::from("check-olean"),
        std::ffi::OsString::from("--json"),
        directory.into_os_string(),
    ]);
    assert_eq!(directory_cli.exit_code, 1, "{}", directory_cli.stderr);
    assert!(
        directory_cli
            .stderr
            .contains("\"class\":\"unresolved-imports\""),
        "directory collection must associate every companion pair before closed-set planning: {}",
        directory_cli.stderr
    );
    assert!(!directory_cli.stderr.contains("missing .olean"));
}

#[test]
fn present_olean_corpus_inventory_is_closed_and_honest() {
    let rig = pin::RigRun::new(pin::PinRig::PresentOleanCorpusInventory);
    let Some(reference_lib) = reference_lib() else {
        eprintln!(
            "{}",
            rig.typed_skip()
                .expect("record the typed present-olean inventory skip")
        );
        return;
    };
    let inventory =
        inventory_present_oleans(&reference_lib).expect("inventory every present pinned olean");
    let order = corpus_module_order(&inventory).expect("present imports have canonical order");
    let oracle_targets = leanchecker_targets(&inventory);
    let oracle_applicable = inventory.decoded - inventory.oracle_skipped;
    eprintln!(
        "kernel_reference_corpus inventory: modules={} decoded={} \
         oracle_applicable={} oracle_skipped={} missing_imports={} oracle_targets={} \
         fixture_hash={}",
        inventory.modules.len(),
        inventory.decoded,
        oracle_applicable,
        inventory.oracle_skipped,
        inventory.missing_imports.len(),
        oracle_targets.len(),
        inventory.fixture_hash
    );
    assert!(
        inventory.modules.len() as u64 >= PINNED_PRESENT_OLEAN_FLOOR,
        "present-olean corpus silently shrank: {} < {} modules",
        inventory.modules.len(),
        PINNED_PRESENT_OLEAN_FLOOR
    );
    assert!(
        inventory.decoded >= PINNED_DECODED_DECL_FLOOR,
        "decoded corpus silently shrank: {} < {} declarations",
        inventory.decoded,
        PINNED_DECODED_DECL_FLOOR
    );
    assert!(
        oracle_applicable >= PINNED_ORACLE_APPLICABLE_FLOOR,
        "leanchecker-applicable corpus silently shrank: {oracle_applicable} < \
         {PINNED_ORACLE_APPLICABLE_FLOOR}"
    );
    assert_eq!(
        inventory.oracle_skipped, 3_612,
        "Lean.Replay applicability census moved; never count skipped rows as accepted"
    );
    assert_eq!(
        order.len(),
        inventory.modules.len(),
        "canonical module order must conserve the present inventory"
    );
    assert!(
        oracle_targets.len() <= 160,
        "leanchecker target cover regressed to an unbounded leaf list: {}",
        oracle_targets.len()
    );
    for module in inventory
        .modules
        .values()
        .filter(|module| module.decoded != 0)
    {
        assert!(
            oracle_targets
                .iter()
                .any(|target| component_prefix(target, &module.name)),
            "leanchecker target cover omitted declaration-bearing module {}",
            module.name
        );
    }
    rig.executed()
        .expect("record the executed present-olean inventory");
}

#[test]
fn present_olean_import_contexts_accept_reference_extended_duplicates() {
    let rig = pin::RigRun::new(pin::PinRig::PresentOleanImportContexts);
    let Some(reference_lib) = reference_lib() else {
        eprintln!(
            "{}",
            rig.typed_skip()
                .expect("record the typed import-context skip")
        );
        return;
    };
    let inventory =
        inventory_present_oleans(&reference_lib).expect("inventory every present pinned olean");
    let order = corpus_module_order(&inventory).expect("present imports have canonical order");
    let order_index = order
        .iter()
        .enumerate()
        .map(|(index, name)| (name.clone(), index))
        .collect::<HashMap<_, _>>();

    struct ContextState {
        closure: BTreeSet<String>,
        context: ReferenceFixtureContext,
        active_infos: Vec<ConstantInfo>,
    }

    let mut states = BTreeMap::<String, ContextState>::new();
    let mut extended_duplicates = 0_u64;
    let mut extended_only_duplicates = 0_u64;
    let mut collision_count = 0_u64;
    let mut first_collisions = Vec::new();
    for module_name in &order {
        let module = &inventory.modules[module_name];
        let infos = decode_corpus_module(&module.path, &module.name)
            .expect("decode governed corpus module")
            .infos;
        let (active_infos, _, _) = reference_active_rows(&infos);
        let direct_imports = module
            .imports
            .iter()
            .filter(|import| {
                inventory.modules.contains_key(*import) && import.as_str() != module.name
            })
            .cloned()
            .collect::<Vec<_>>();
        let mut closure = BTreeSet::new();
        for import in &direct_imports {
            let state = states
                .get(import)
                .expect("canonical module order places every present import first");
            closure.insert(import.clone());
            closure.extend(state.closure.iter().cloned());
        }
        let base = direct_imports
            .iter()
            .max_by_key(|import| states[*import].closure.len());
        let (mut context, mut included) = match base {
            Some(base) => {
                let state = &states[base];
                let mut included = state.closure.clone();
                included.insert(base.clone());
                (state.context.clone(), included)
            }
            None => (ReferenceFixtureContext::new(), BTreeSet::new()),
        };
        let mut missing = closure.difference(&included).cloned().collect::<Vec<_>>();
        missing.sort_by_key(|name| order_index[name]);
        for dependency in missing {
            let state = &states[&dependency];
            let (next, report) =
                extend_reference_fixture_environment(context, &state.active_infos, &dependency)
                    .expect("merge a decoded import contribution");
            context = next;
            included.insert(dependency.clone());
            extended_duplicates = extended_duplicates
                .checked_add(report.extended_duplicates)
                .expect("extended-duplicate census overflow");
            extended_only_duplicates = extended_only_duplicates
                .checked_add(report.extended_only_duplicates)
                .expect("extended-only duplicate census overflow");
            collision_count = collision_count
                .checked_add(
                    u64::try_from(report.collisions.len())
                        .expect("collision count must fit the evidence schema"),
                )
                .expect("collision census overflow");
            for name in report.collisions {
                if first_collisions.len() < 20 {
                    first_collisions.push(format!("{} <- {dependency}: {name}", module.name));
                }
            }
        }
        assert_eq!(
            included, closure,
            "{} import-context reconstruction omitted a present dependency",
            module.name
        );
        let (context, report) =
            extend_reference_fixture_environment(context, &active_infos, &module.name)
                .expect("publish decoded module into fixture context");
        extended_duplicates = extended_duplicates
            .checked_add(report.extended_duplicates)
            .expect("extended-duplicate census overflow");
        extended_only_duplicates = extended_only_duplicates
            .checked_add(report.extended_only_duplicates)
            .expect("extended-only duplicate census overflow");
        collision_count = collision_count
            .checked_add(
                u64::try_from(report.collisions.len())
                    .expect("collision count must fit the evidence schema"),
            )
            .expect("collision census overflow");
        for name in report.collisions {
            if first_collisions.len() < 20 {
                first_collisions.push(format!("{} <- self: {name}", module.name));
            }
        }
        states.insert(
            module.name.clone(),
            ContextState {
                closure,
                context,
                active_infos,
            },
        );
    }

    eprintln!(
        "kernel_reference_corpus context_adapter: modules={} \
         extended_duplicates={} extended_only_duplicates={} collisions={}",
        states.len(),
        extended_duplicates,
        extended_only_duplicates,
        collision_count
    );
    assert_eq!(
        states.len(),
        inventory.modules.len(),
        "context adapter must cover every present module"
    );
    assert!(
        extended_duplicates > 0,
        "the pin must exercise real duplicate acceptance in reconstructed import contexts"
    );
    assert_eq!(
        collision_count, 0,
        "valid pinned import closures must all be representable; first={first_collisions:?}"
    );
    rig.executed()
        .expect("record the executed present-olean import-context differential");
}

/// One module's accumulated state in the canonical corpus walk: the PRESENT-import
/// closure it was reconstructed from, the fixture context that closure produces, its
/// decoded active rows, and whether that reconstruction was faithfully representable.
struct CorpusFixtureState {
    closure: BTreeSet<String>,
    context: ReferenceFixtureContext,
    active_infos: Vec<ConstantInfo>,
    faithful: bool,
}

/// One module's reconstructed import context, plus the merge findings that decided
/// whether it is faithfully representable. `collisions` is `(dependency, colliding
/// names)` in merge order and is empty exactly when `faithful` is not falsified here.
struct ReconstructedImportContext {
    imported: ReferenceFixtureContext,
    closure: BTreeSet<String>,
    faithful: bool,
    collisions: Vec<(String, Vec<String>)>,
}

/// Rebuild exactly the union of a module's PRESENT direct-import closures from decoded
/// rows. Starting from the largest direct import preserves structural sharing; only
/// contributions absent from that base are inserted.
///
/// **Why this is shared rather than copied** (R2 of bead `fln-corpus-thread-matrix-93te`).
/// The corpus census (`pinned_present_olean_kernel_differential`) scores verdicts produced
/// in these environments; the corpus thread matrix
/// (`present_olean_corpus_thread_matrix_compares_stream_digests`) compares stream digests
/// produced in them. A second copy would let the two drift, and the matrix's digests would
/// then be evidence about a computation the census does not perform — with nothing
/// objecting, because each test would still read as internally consistent. That is exactly
/// the join-between-two-artifacts defect AGENTS.md item 7 records, and it is the same
/// argument that made R3 extract `first_divergence_across_widths` instead of writing a
/// second comparator.
fn reconstruct_import_context(
    module: &CorpusModule,
    inventory: &CorpusInventory,
    order_index: &HashMap<String, usize>,
    states: &BTreeMap<String, CorpusFixtureState>,
) -> ReconstructedImportContext {
    let direct_imports = module
        .imports
        .iter()
        .filter(|import| inventory.modules.contains_key(*import) && import.as_str() != module.name)
        .cloned()
        .collect::<Vec<_>>();
    let mut closure = BTreeSet::new();
    let mut faithful = true;
    for import in &direct_imports {
        let state = states
            .get(import)
            .unwrap_or_else(|| panic!("{} imported before {import}", module.name));
        closure.insert(import.clone());
        closure.extend(state.closure.iter().cloned());
        faithful &= state.faithful;
    }
    let base = direct_imports
        .iter()
        .max_by_key(|import| states[*import].closure.len());
    let (mut imported, mut included) = match base {
        Some(base) => {
            let state = &states[base];
            let mut included = state.closure.clone();
            included.insert(base.clone());
            (state.context.clone(), included)
        }
        None => (ReferenceFixtureContext::new(), BTreeSet::new()),
    };
    let mut missing = closure.difference(&included).cloned().collect::<Vec<_>>();
    missing.sort_by_key(|name| order_index[name]);
    let mut collisions = Vec::new();
    for dependency in missing {
        let state = &states[&dependency];
        let (next, merge) =
            extend_reference_fixture_environment(imported, &state.active_infos, &dependency)
                .expect("merge a decoded import contribution");
        imported = next;
        included.insert(dependency.clone());
        if !merge.collisions.is_empty() {
            faithful = false;
            collisions.push((dependency, merge.collisions));
        }
    }
    assert_eq!(
        included, closure,
        "{} import-context reconstruction omitted a present dependency",
        module.name
    );
    ReconstructedImportContext {
        imported,
        closure,
        faithful,
        collisions,
    }
}

/// One completed run of the corpus thread matrix, retained (bead `franken_lean-p6x1`).
///
/// **Why anything is retained at all.** A run that leaves nothing behind cannot be told
/// apart later from a run that never happened, and the sentences in AGENTS.md and README
/// that describe the observation would then rest on a memory. The row binds the three
/// things that decide whether the observation is about *this* world: the Reference pin,
/// the corpus revision (`corpus_fixture_hash`, which is the inventory's own hash over
/// every present module and its bytes), and the host it ran on.
///
/// **Why the file is keyed by pin rather than by date.** The receipt lives at
/// `evidence/corpus_thread_matrix/<pin>.jsonl`, so the path itself carries the binding the
/// waiver expires on: when `SUITE.lock` advances the Reference, the file for the new epoch
/// does not exist and the guard fails. Nothing has to remember a date, and nothing has to
/// read a clock — which matters, because a gate that reads the wall clock returns
/// different answers for the same inputs and contradicts FL-INV-01 on the way to enforcing
/// it.
///
/// **`lane_source_digest_at_run` is provenance, not freshness.** It is the lane file under
/// the project hasher (`Domain::Fixture`, the same algorithm every other digest here uses),
/// computed by the run over its own source so it cannot be forgotten or mistyped. It records
/// which source
/// produced the row and never becomes false. It is deliberately NOT gated: the cone that
/// invalidates the observation (`fln-kernel`, `fln-env`, `fln-core`, `fln-hash`) took 148
/// commits in the seven days before this bead, so a gate on it would be red several times
/// a day with a 32-minute clear. A red that fires that often is one everybody learns to
/// ignore — a ritual, not a guard. That churn is also the honest reason the class is
/// `bounded_model` and not an invariant, and it is recorded here rather than smoothed over.
#[derive(Clone, PartialEq, Eq)]
struct CorpusMatrixReceipt {
    bead: String,
    pin: String,
    observed_unix_s: u64,
    corpus_fixture_hash: String,
    modules: u64,
    decoded: u64,
    units_compared: u64,
    widths: Vec<u64>,
    corpus_digests: Vec<String>,
    diverging_modules: u64,
    unmatrixed_modules: u64,
    wall_ms: u64,
    per_width_ms: Vec<u64>,
    profile: String,
    target: String,
    available_parallelism: u64,
    lane_source_digest_at_run: String,
    class: String,
}

const CORPUS_MATRIX_RECEIPT_SCHEMA: &str = "fln.corpus-thread-matrix-receipt/1";

impl CorpusMatrixReceipt {
    /// The canonical one-line form. Field order is fixed and is part of the format: a
    /// receipt that does not re-serialize to the bytes it was read from is refused rather
    /// than repaired, so there is exactly one spelling of a given observation.
    fn to_row(&self) -> String {
        let numbers = |values: &[u64]| {
            values
                .iter()
                .map(u64::to_string)
                .collect::<Vec<_>>()
                .join(",")
        };
        let strings = |values: &[String]| {
            values
                .iter()
                .map(|value| json_string(value))
                .collect::<Vec<_>>()
                .join(",")
        };
        format!(
            "{{\"schema\":{},\"bead\":{},\"pin\":{},\"observed_unix_s\":{},\
             \"corpus_fixture_hash\":{},\"modules\":{},\"decoded\":{},\"units_compared\":{},\
             \"widths\":[{}],\"corpus_digests\":[{}],\"diverging_modules\":{},\
             \"unmatrixed_modules\":{},\"wall_ms\":{},\"per_width_ms\":[{}],\"profile\":{},\
             \"target\":{},\"available_parallelism\":{},\"lane_source_digest_at_run\":{},\
             \"class\":{}}}",
            json_string(CORPUS_MATRIX_RECEIPT_SCHEMA),
            json_string(&self.bead),
            json_string(&self.pin),
            self.observed_unix_s,
            json_string(&self.corpus_fixture_hash),
            self.modules,
            self.decoded,
            self.units_compared,
            numbers(&self.widths),
            strings(&self.corpus_digests),
            self.diverging_modules,
            self.unmatrixed_modules,
            self.wall_ms,
            numbers(&self.per_width_ms),
            json_string(&self.profile),
            json_string(&self.target),
            self.available_parallelism,
            json_string(&self.lane_source_digest_at_run),
            json_string(&self.class),
        )
    }

    /// Read a row, then prove the read was faithful by re-serializing it.
    ///
    /// Extraction is by key and so tolerant of order; the round-trip is what makes the
    /// format strict. A parser that silently accepted a row it could not reproduce would
    /// let the guard below check a value nobody wrote — the same join defect one floor
    /// down, between a file and the meaning taken from it.
    fn from_row(row: &str) -> Result<CorpusMatrixReceipt, String> {
        fn text(row: &str, key: &str) -> Result<String, String> {
            let needle = format!("\"{key}\":\"");
            let start = row
                .find(&needle)
                .ok_or_else(|| format!("missing string field `{key}`"))?
                + needle.len();
            let rest = &row[start..];
            let end = rest
                .find('"')
                .ok_or_else(|| format!("unterminated string field `{key}`"))?;
            Ok(rest[..end].to_string())
        }
        fn number(row: &str, key: &str) -> Result<u64, String> {
            let needle = format!("\"{key}\":");
            let start = row
                .find(&needle)
                .ok_or_else(|| format!("missing numeric field `{key}`"))?
                + needle.len();
            let rest = &row[start..];
            let end = rest
                .find(|c: char| !c.is_ascii_digit())
                .unwrap_or(rest.len());
            rest[..end]
                .parse()
                .map_err(|_| format!("field `{key}` is not a u64"))
        }
        fn array<'a>(row: &'a str, key: &str) -> Result<&'a str, String> {
            let needle = format!("\"{key}\":[");
            let start = row
                .find(&needle)
                .ok_or_else(|| format!("missing array field `{key}`"))?
                + needle.len();
            let rest = &row[start..];
            let end = rest
                .find(']')
                .ok_or_else(|| format!("unterminated array field `{key}`"))?;
            Ok(&rest[..end])
        }
        let numbers = |key: &str| -> Result<Vec<u64>, String> {
            array(row, key)?
                .split(',')
                .filter(|item| !item.is_empty())
                .map(|item| {
                    item.parse::<u64>()
                        .map_err(|_| format!("array `{key}` holds a non-u64"))
                })
                .collect()
        };
        let strings = |key: &str| -> Result<Vec<String>, String> {
            Ok(array(row, key)?
                .split(',')
                .filter(|item| !item.is_empty())
                .map(|item| item.trim_matches('"').to_string())
                .collect())
        };
        let schema = text(row, "schema")?;
        if schema != CORPUS_MATRIX_RECEIPT_SCHEMA {
            return Err(format!(
                "receipt schema is `{schema}`, expected `{CORPUS_MATRIX_RECEIPT_SCHEMA}`"
            ));
        }
        let receipt = CorpusMatrixReceipt {
            bead: text(row, "bead")?,
            pin: text(row, "pin")?,
            observed_unix_s: number(row, "observed_unix_s")?,
            corpus_fixture_hash: text(row, "corpus_fixture_hash")?,
            modules: number(row, "modules")?,
            decoded: number(row, "decoded")?,
            units_compared: number(row, "units_compared")?,
            widths: numbers("widths")?,
            corpus_digests: strings("corpus_digests")?,
            diverging_modules: number(row, "diverging_modules")?,
            unmatrixed_modules: number(row, "unmatrixed_modules")?,
            wall_ms: number(row, "wall_ms")?,
            per_width_ms: numbers("per_width_ms")?,
            profile: text(row, "profile")?,
            target: text(row, "target")?,
            available_parallelism: number(row, "available_parallelism")?,
            lane_source_digest_at_run: text(row, "lane_source_digest_at_run")?,
            class: text(row, "class")?,
        };
        if receipt.to_row() != row {
            return Err(format!(
                "receipt is not in canonical form; it was read as\n  {}\nbut the file holds\n  {row}",
                receipt.to_row()
            ));
        }
        Ok(receipt)
    }

    /// Everything the row must say to be evidence for the sentences that cite it.
    ///
    /// **Why this is a function and not assertions inside the guard.** It has two callers:
    /// the retention guard, which runs it over the committed file, and
    /// `a_receipt_that_compared_nothing_is_refused`, which runs it over forged rows. A
    /// second copy of these rules written for the mutant test could drift from the one that
    /// actually gates, and then the mutants would prove a check that no longer runs — the
    /// join defect this file is otherwise careful about, one level up.
    ///
    /// **What the checks are for.** The first version of this guard tested the pin, the
    /// widths, `diverging_modules == 0`, digest equality and the class token, and nothing
    /// about *size*. That is `bkw6`'s empty-referent shape: a row recording
    /// `modules: 0, decoded: 0, units_compared: 0, corpus_digests: []` satisfied every one
    /// of those — zero divergences over zero comparisons — and stood as the retained
    /// evidence for "2433 modules, every stream identical at {1, 8, 32}". Measured at
    /// `2ebe03e0`: the vacuous row passed, a wrong-pin row failed, so the guard was reading
    /// the file and simply had nothing to say about what the row claimed to have done.
    ///
    /// The producer cannot emit such a row — it asserts the current live coverage floors
    /// before it compares anything and refuses a single unmatrixed module. But the producer
    /// is not what stands between the documents and the file: this is. The retained v1 row
    /// predates module-part decoding, so its anti-vacuity floor is the public-region
    /// population it actually observed (`RETAINED_MATRIX_V1_DECODED_DECL_FLOOR`), not the
    /// larger live inventory a later decoder exposed. Recasting the old row as a current run
    /// would be fabricated evidence; accepting less than its measured population would make
    /// the guard vacuous.
    ///
    /// The floors are `>=`: a larger corpus is not a failure, a smaller one is.
    fn validate(&self, pin: &str) -> Result<(), String> {
        if self.pin != pin {
            return Err(format!(
                "row records pin {} but the file is the {pin} epoch's. The path IS the \
                 binding; a row filed under the wrong epoch would make the guard check an \
                 observation of another Reference",
                self.pin
            ));
        }
        let widths = CORPUS_MATRIX_WIDTHS
            .iter()
            .map(|w| *w as u64)
            .collect::<Vec<_>>();
        if self.widths != widths {
            return Err(format!(
                "row records widths {:?}, but the lane runs {CORPUS_MATRIX_WIDTHS:?}. An \
                 observation at other widths is not evidence for the widths PG-5 names",
                self.widths
            ));
        }

        // CARDINALITY, and it comes before the content checks below on purpose. `all()` over
        // an empty collection is vacuously true, so an absent digest list would satisfy
        // "every width agreed" by having no widths to disagree. Counting first makes that
        // unreachable instead of merely unlikely, and it is what lets the equality check
        // index element zero at all.
        if self.corpus_digests.len() != self.widths.len() {
            return Err(format!(
                "row claims widths {:?} but carries {} corpus digest(s). A width with no \
                 digest was never folded, so the row cannot be evidence that it agreed",
                self.widths,
                self.corpus_digests.len()
            ));
        }
        if self.per_width_ms.len() != self.widths.len() {
            return Err(format!(
                "row claims widths {:?} but carries {} per-width timing(s). A width with no \
                 measured time was not run",
                self.widths,
                self.per_width_ms.len()
            ));
        }

        // COVERAGE — the producer's own preconditions, re-derived from the producer's own
        // constants so the two cannot drift apart.
        if self.unmatrixed_modules != 0 {
            return Err(format!(
                "row records {} unmatrixed module(s). The lane refuses to publish an \
                 observation with any module left out of the matrix, because the claim would \
                 then be about a subset nobody named",
                self.unmatrixed_modules
            ));
        }
        if self.modules < PINNED_PRESENT_OLEAN_FLOOR {
            return Err(format!(
                "row records {} matrixed module(s), below the pinned present-module floor of \
                 {PINNED_PRESENT_OLEAN_FLOOR} the lane asserts before it compares anything. \
                 Zero divergences over a corpus this small is not the observation the \
                 documents cite",
                self.modules
            ));
        }
        if self.decoded < RETAINED_MATRIX_V1_DECODED_DECL_FLOOR {
            return Err(format!(
                "row records {} decoded declaration(s) in matrixed modules, below the pinned \
                 retained-v1 floor of {RETAINED_MATRIX_V1_DECODED_DECL_FLOOR}",
                self.decoded
            ));
        }
        // PROVENANCE IN TIME. Until bead `franken_lean-p6x1` this field was written by the
        // producer, serialized, parsed and re-serialized, and asserted on by NOTHING — the one
        // datum separating a run that happened from a row that was filed, consumed by no
        // check. It is now load-bearing: the retention guard renders it into the marker both
        // documents must carry, so a zero here would put `1970-01-01` into AGENTS.md and
        // README and hold them to it. Refused rather than rendered, because a broken
        // measurement must not be reported as a measurement.
        //
        // This is deliberately NOT a freshness bound. No comparison against the wall clock
        // appears here or in the guard: an old observation is a disclosed old observation, not
        // a failure. The only rejection is a timestamp that cannot be a real instant.
        if self.observed_unix_s == 0 {
            return Err(
                "row records observed_unix_s: 0. A receipt with no observation instant cannot \
                 date the evidence it carries, and the retention guard would render it into \
                 both documents as 1970-01-01. The producer sets this from the clock at the \
                 end of the run, so zero means the row was constructed rather than observed"
                    .to_string(),
            );
        }
        if self.units_compared == 0 {
            return Err(
                "row records zero units compared. `diverging_modules: 0` over zero \
                 comparisons is not agreement; it is the absence of a measurement wearing \
                 the shape of one"
                    .to_string(),
            );
        }
        if self.units_compared > self.decoded {
            return Err(format!(
                "row records {} units compared but only {} decoded declaration(s) to compare; \
                 the row contradicts itself",
                self.units_compared, self.decoded
            ));
        }
        if self.wall_ms == 0 {
            return Err(
                "row records wall_ms: 0. The whole corpus at three widths does not complete \
                 in under a millisecond, and this number is the priced input to the cadence \
                 decision the PG-5 waiver rests on"
                    .to_string(),
            );
        }

        // PROVENANCE. These two fields are what bind the row to a corpus revision and to the
        // source that produced it. Empty strings are not weak provenance, they are none.
        if self.corpus_fixture_hash.is_empty() {
            return Err(
                "row carries an empty corpus_fixture_hash, so it names no corpus revision"
                    .to_string(),
            );
        }
        if self.lane_source_digest_at_run.is_empty() {
            return Err(
                "row carries an empty lane_source_digest_at_run, so it names no producing \
                 source"
                    .to_string(),
            );
        }

        // CONTENT.
        if self.diverging_modules != 0 {
            return Err(format!(
                "row records {} diverging module(s). A refutation must not sit quietly in an \
                 evidence file while the documents claim schedule-independence — this is \
                 release-blocking, not a receipt",
                self.diverging_modules
            ));
        }
        if !self
            .corpus_digests
            .iter()
            .all(|digest| *digest == self.corpus_digests[0])
        {
            return Err(
                "per-width corpus digests differ while diverging_modules is 0; the row \
                 contradicts itself"
                    .to_string(),
            );
        }
        if self.class != "observed_once_not_an_invariant" {
            return Err(format!(
                "row claims class {}, which this lane cannot earn",
                self.class
            ));
        }
        Ok(())
    }
}

/// Where the retained receipts for a given Reference pin live, relative to this crate.
fn corpus_matrix_receipt_path(pin: &str) -> PathBuf {
    fln_conformance::checked_manifest_dir!()
        .join("evidence/corpus_thread_matrix")
        .join(format!("{pin}.jsonl"))
}

/// The Reference pin `SUITE.lock` currently governs — the one ceremony that moves it.
fn suite_lock_reference_pin() -> String {
    const SUITE_LOCK: &str = include_str!("../../../SUITE.lock");
    SUITE_LOCK
        .lines()
        .find(|line| line.starts_with("reference "))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|token| token.strip_prefix("tag="))
        })
        .expect("SUITE.lock must pin the Reference with a tag= field")
        .to_string()
}

/// The corpus revision is an input identity, not a directory name: a corpus
/// checkout at another revision can be complete and still cannot substantiate
/// the pinned whole-corpus lane.
fn suite_lock_corpus_commit() -> String {
    const SUITE_LOCK: &str = include_str!("../../../SUITE.lock");
    SUITE_LOCK
        .lines()
        .find(|line| line.starts_with("corpus "))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|token| token.strip_prefix("commit="))
        })
        .expect("SUITE.lock must pin the corpus with a commit= field")
        .to_string()
}

/// Corpus provisioning is host state, never a repository fixture. Keep the
/// discovery seam in one place so the resurrection sweep and later kernel
/// differential cannot disagree on what they accepted as the Mathlib corpus.
fn mathlib_corpus_root() -> PathBuf {
    std::env::var_os("FLN_MATHLIB_CORPUS")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("/data/tmp/mathlib4-corpus"))
}

/// Refuse before an expensive whole-corpus run when its external input cannot
/// identify itself. This is intentionally stronger than `is_dir()`: a different
/// Mathlib commit, a symlinked checkout, or a source-only checkout would make a
/// seemingly successful sweep evidence about the wrong world.
fn preflight_mathlib_corpus() -> Result<PathBuf, String> {
    let corpus = mathlib_corpus_root();
    let metadata = fs::symlink_metadata(&corpus)
        .map_err(|error| format!("corpus root {} is unavailable: {error}", corpus.display()))?;
    if metadata.file_type().is_symlink() || !metadata.is_dir() {
        return Err(format!(
            "corpus root {} must be a real directory, not a symlink or non-directory",
            corpus.display()
        ));
    }
    let output = Command::new("git")
        .args(["-C"])
        .arg(&corpus)
        .args(["rev-parse", "--verify", "HEAD^{commit}"])
        .output()
        .map_err(|error| {
            format!(
                "cannot inspect corpus checkout {}: {error}",
                corpus.display()
            )
        })?;
    if !output.status.success() {
        return Err(format!(
            "corpus root {} is not a readable git checkout: {}",
            corpus.display(),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    let actual = String::from_utf8_lossy(&output.stdout).trim().to_string();
    let expected = suite_lock_corpus_commit();
    if actual != expected {
        return Err(format!(
            "corpus commit {actual} != SUITE.lock corpus commit {expected}"
        ));
    }
    let library = corpus.join(".lake/build/lib/lean/Mathlib");
    let library_metadata = fs::symlink_metadata(&library).map_err(|error| {
        format!(
            "pinned corpus has no built Mathlib olean root {}: {error}",
            library.display()
        )
    })?;
    if library_metadata.file_type().is_symlink() || !library_metadata.is_dir() {
        return Err(format!(
            "built Mathlib olean root {} must be a real directory",
            library.display()
        ));
    }
    Ok(library)
}

/// The cheap first gate for `franken_lean-t6r7`: establish that a full
/// resurrection walk has the exact corpus it names before it touches thousands
/// of oleans. It is on demand because host provisioning is an external input;
/// a missing corpus emits a typed BLOCKED row and fails rather than becoming a
/// green zero-module scan.
///
/// Run explicitly:
/// `cargo test --locked -p fln-conformance --test kernel_replay \
///   whole_mathlib_corpus_resurrection_preflight -- --ignored --exact --nocapture`
#[test]
#[ignore = "on-demand host preflight for the whole-Mathlib corpus lane (franken_lean-t6r7)"]
fn whole_mathlib_corpus_resurrection_preflight() {
    match preflight_mathlib_corpus() {
        Ok(library) => {
            let mut paths = Vec::new();
            collect_present_oleans(&library, &mut paths)
                .expect("enumerate the pinned built Mathlib corpus");
            paths.sort();
            assert!(
                paths.len() >= 8_000,
                "whole-Mathlib preflight found only {} oleans under {}; a truncated corpus is not a smaller green sweep",
                paths.len(),
                library.display()
            );
            println!(
                "{{\"schema\":\"fln-t6r7-mathlib-preflight/1\",\"status\":\"ready\",\"corpus_commit\":{},\"mathlib_oleans\":{}}}",
                json_string(&suite_lock_corpus_commit()),
                paths.len(),
            );
        }
        Err(reason) => {
            println!(
                "{{\"schema\":\"fln-t6r7-mathlib-preflight/1\",\"status\":\"blocked\",\"reason\":{}}}",
                json_string(&reason),
            );
            panic!("whole-Mathlib corpus preflight blocked: {reason}");
        }
    }
}

struct WholeMathlibCorpus {
    mathlib_modules: Vec<String>,
    roots: Vec<(String, PathBuf)>,
    inventory: CorpusInventory,
}

fn closed_whole_mathlib_corpus(reference_lib: &Path) -> Result<WholeMathlibCorpus, String> {
    let library = preflight_mathlib_corpus()?;
    let mathlib_modules = module_names_below(&library, Some("Mathlib"))?;
    let roots = chosen_set_roots(reference_lib);
    for (_, root) in &roots {
        if !root.is_dir() {
            return Err(format!(
                "whole-Mathlib closure root missing: {}",
                root.display()
            ));
        }
    }
    let inventory = closure_inventory_from_seeds(&roots, &mathlib_modules)?;
    if !inventory.missing_imports.is_empty() {
        return Err(format!(
            "whole-Mathlib closure has unresolved imports: {:?}",
            inventory
                .missing_imports
                .iter()
                .take(20)
                .collect::<Vec<_>>()
        ));
    }
    Ok(WholeMathlibCorpus {
        mathlib_modules,
        roots,
        inventory,
    })
}

/// Decode the entire built Mathlib import closure before attempting replay. The
/// old sweep decoded only paths below `Mathlib/`: its order silently ignored
/// every `Init`, `Std`, `Lean`, and package import because those modules were
/// absent from the inventory. This walk seeds all built `Mathlib.*` modules into
/// the same multi-root closure builder used by the executable selected probes,
/// and refuses unless that transitive closure is actually closed.
///
/// This still makes no kernel-admission claim. It closes the artifact/context
/// input seam needed by that later lane rather than relabelling decode as replay.
///
/// Run explicitly after the preflight is ready:
/// `cargo test --locked -p fln-conformance --test kernel_replay \
///   whole_mathlib_corpus_resurrection_sweep -- --ignored --exact --nocapture`
#[test]
#[ignore = "cost: decode the full pinned Mathlib corpus; on-demand resurrection sweep for franken_lean-t6r7"]
fn whole_mathlib_corpus_resurrection_sweep() {
    let reference_lib =
        reference_lib().expect("pinned Reference stdlib required for the Mathlib closure");
    let WholeMathlibCorpus {
        mathlib_modules,
        roots: _,
        inventory,
    } = closed_whole_mathlib_corpus(&reference_lib)
        .expect("decode the closed whole-Mathlib import graph");
    assert!(
        mathlib_modules.len() >= 8_000,
        "whole-Mathlib resurrection found only {} modules; a truncated corpus is not a smaller green sweep",
        mathlib_modules.len(),
    );
    assert!(
        mathlib_modules
            .iter()
            .all(|name| inventory.modules.contains_key(name)),
        "the closure inventory omitted at least one Mathlib seed"
    );
    let mathlib_decoded = mathlib_modules
        .iter()
        .map(|name| inventory.modules[name].decoded)
        .sum::<u64>();
    assert!(
        mathlib_decoded != 0,
        "whole-Mathlib resurrection decoded zero declarations"
    );
    assert!(
        mathlib_modules
            .iter()
            .all(|name| name.starts_with("Mathlib.")),
        "the Mathlib seeds must be namespace-qualified before resolving their imports"
    );
    let order = corpus_module_order(&inventory).expect("derive canonical Mathlib module order");
    assert_eq!(
        order.len(),
        inventory.modules.len(),
        "canonical order must cover the complete decoded import closure"
    );
    println!(
        "{{\"schema\":\"fln-t6r7-mathlib-resurrection/2\",\"status\":\"observed\",\"corpus_commit\":{},\"mathlib_modules\":{},\"closure_modules\":{},\"mathlib_decoded\":{},\"closure_decoded\":{},\"closure_oracle_skipped\":{},\"missing_imports\":{},\"fixture_hash\":{}}}",
        json_string(&suite_lock_corpus_commit()),
        mathlib_modules.len(),
        inventory.modules.len(),
        mathlib_decoded,
        inventory.decoded,
        inventory.oracle_skipped,
        inventory.missing_imports.len(),
        json_string(&inventory.fixture_hash),
    );
}

/// The full pinned Mathlib kernel differential over the exact closed graph
/// established by `whole_mathlib_corpus_resurrection_sweep`. It reuses the
/// Reference-library corpus scorer and reconstructed-context executor; only
/// the seed set and sealed oracle search roots differ.
///
/// This is intentionally on demand. A run is one bounded observation at this
/// pin/corpus/host, and any subject resource exhaustion remains an unscorable
/// non-answer. Run explicitly:
///
/// `cargo test --locked -p fln-conformance --test kernel_replay \
///   whole_mathlib_kernel_differential -- --ignored --exact --nocapture`
#[test]
#[ignore = "cost: replay the exact closed whole-Mathlib graph through both kernels; on-demand bounded observation"]
fn whole_mathlib_kernel_differential() {
    let reference_lib =
        reference_lib().expect("pinned Reference stdlib required for the Mathlib differential");
    let WholeMathlibCorpus {
        mathlib_modules,
        roots,
        inventory,
    } = closed_whole_mathlib_corpus(&reference_lib)
        .expect("inventory the exact closed whole-Mathlib graph");
    assert!(
        mathlib_modules.len() >= 8_000,
        "whole-Mathlib differential seed floor: {} < 8000",
        mathlib_modules.len()
    );
    let mathlib_oracle_applicable = mathlib_modules
        .iter()
        .map(|name| {
            let module = &inventory.modules[name];
            module.decoded - module.oracle_skipped
        })
        .sum::<u64>();
    assert!(
        mathlib_oracle_applicable != 0,
        "whole-Mathlib differential has no oracle-applicable declarations"
    );
    let order = corpus_module_order(&inventory).expect("canonical whole-Mathlib module order");
    let search_roots = roots
        .iter()
        .map(|(_, root)| root.as_path())
        .collect::<Vec<_>>();
    run_accepted_corpus_kernel_differential(
        &reference_lib,
        &search_roots,
        inventory,
        order,
        CorpusDifferentialScope {
            module_floor: 10_000,
            decoded_floor: 700_000,
            compared_floor: mathlib_oracle_applicable,
            oracle_total_timeout: WHOLE_MATHLIB_ORACLE_TOTAL_TIMEOUT,
            oracle_process_timeout: WHOLE_MATHLIB_ORACLE_PROCESS_TIMEOUT,
            oracle_modules_per_process: WHOLE_MATHLIB_ORACLE_MODULES_PER_PROCESS,
            label: "pinned-whole-mathlib",
        },
    );
}

/// The executable corpus obligation. It remains ignored while fln-7odd is
/// open because the selected oracle itself supplies no verdict for 3,612
/// decoded rows; enabling a gate that is known to fail before that contract is
/// decided would make every ordinary `cargo test` unusable. Run explicitly:
///
/// `cargo test -p fln-conformance --test kernel_replay \
///  pinned_present_olean_kernel_differential -- --ignored --exact --nocapture`
#[test]
#[ignore = "blocked by fln-7odd: leanchecker skips unsafe and partial declarations"]
fn pinned_present_olean_kernel_differential() {
    let reference_lib =
        reference_lib().expect("pinned Reference stdlib required for the live corpus differential");
    let inventory =
        inventory_present_oleans(&reference_lib).expect("inventory every present pinned olean");
    let order = corpus_module_order(&inventory).expect("canonical present-module order");
    let search_roots = [reference_lib.as_path()];
    run_accepted_corpus_kernel_differential(
        &reference_lib,
        &search_roots,
        inventory,
        order,
        CorpusDifferentialScope {
            module_floor: PINNED_PRESENT_OLEAN_FLOOR,
            decoded_floor: PINNED_DECODED_DECL_FLOOR,
            compared_floor: PINNED_ORACLE_APPLICABLE_FLOOR,
            oracle_total_timeout: DEFAULT_LEANCHECKER_TIMEOUT,
            oracle_process_timeout: DEFAULT_LEANCHECKER_TIMEOUT,
            oracle_modules_per_process: usize::MAX,
            label: "pinned-reference-library",
        },
    );
}

struct CorpusDifferentialScope {
    module_floor: u64,
    decoded_floor: u64,
    compared_floor: u64,
    oracle_total_timeout: Duration,
    oracle_process_timeout: Duration,
    oracle_modules_per_process: usize,
    label: &'static str,
}

fn run_accepted_corpus_kernel_differential(
    reference_lib: &Path,
    oracle_search_roots: &[&Path],
    inventory: CorpusInventory,
    order: Vec<String>,
    scope: CorpusDifferentialScope,
) {
    let CorpusDifferentialScope {
        module_floor,
        decoded_floor,
        compared_floor,
        oracle_total_timeout,
        oracle_process_timeout,
        oracle_modules_per_process,
        label: corpus_label,
    } = scope;
    assert!(
        inventory.modules.len() as u64 >= module_floor,
        "{corpus_label} module coverage floor: {} < {module_floor}",
        inventory.modules.len()
    );
    assert!(
        inventory.decoded >= decoded_floor,
        "{corpus_label} decoded-declaration coverage floor: {} < {decoded_floor}",
        inventory.decoded
    );
    let (oracle, oracle_source) = reference_verdict_with_resume(
        reference_lib,
        oracle_search_roots,
        &inventory,
        oracle_total_timeout,
        oracle_process_timeout,
        oracle_modules_per_process,
    )
    .expect("run pinned leanchecker");
    match oracle {
        ReferenceCorpusVerdict::Accepted {
            duration,
            stdout,
            stderr,
        } => {
            eprintln!(
                "kernel_reference_corpus oracle: verdict=accepted source={} \
                 duration_ms={} stdout_bytes={} stderr_bytes={}",
                oracle_source,
                duration.as_millis(),
                stdout.len(),
                stderr.len()
            );
        }
        ReferenceCorpusVerdict::Rejected {
            status,
            duration,
            stdout,
            stderr,
        } => {
            eprintln!(
                "kernel_reference_corpus oracle: verdict=rejected status={} \
                 duration_ms={} stdout={} stderr={}",
                status,
                duration.as_millis(),
                stdout.lines().take(20).collect::<Vec<_>>().join(" | "),
                stderr.lines().take(20).collect::<Vec<_>>().join(" | ")
            );
            eprintln!(
                "kernel_reference_corpus SUMMARY: 0 of {} decoded declarations compared, \
                 0 disagreements, split by direction: unsoundly_permissive=0 \
                 restrictive_with_carve_out=0 restrictive_without_carve_out=0; \
                 unscorable={}",
                inventory.decoded, inventory.decoded
            );
            panic!(
                "module-level oracle rejection cannot be assigned to individual decoded declarations"
            );
        }
        ReferenceCorpusVerdict::NoAnswer {
            reason,
            duration,
            stdout,
            stderr,
        } => {
            eprintln!(
                "kernel_reference_corpus oracle: verdict=no_answer reason={} \
                 duration_ms={} stdout={} stderr={}",
                reason,
                duration.as_millis(),
                stdout.lines().take(20).collect::<Vec<_>>().join(" | "),
                stderr.lines().take(20).collect::<Vec<_>>().join(" | ")
            );
            eprintln!(
                "kernel_reference_corpus SUMMARY: 0 of {} decoded declarations compared, \
                 0 disagreements, split by direction: unsoundly_permissive=0 \
                 restrictive_with_carve_out=0 restrictive_without_carve_out=0; \
                 unscorable={}",
                inventory.decoded, inventory.decoded
            );
            panic!("a Reference non-answer agrees with nothing");
        }
    }

    let order_index = order
        .iter()
        .enumerate()
        .map(|(index, name)| (name.clone(), index))
        .collect::<HashMap<_, _>>();
    let mut states = BTreeMap::<String, CorpusFixtureState>::new();
    let mut total = CorpusCounts::default();
    for (index, module_name) in order.iter().enumerate() {
        let module = &inventory.modules[module_name];
        let decoded_module = decode_corpus_module(&module.path, &module.name)
            .expect("decode governed corpus module");
        let current_hash = decoded_module.olean_hash;
        let infos = decoded_module.infos;
        assert_eq!(
            current_hash, module.olean_hash,
            "{} changed between inventory and replay",
            module.name
        );
        assert_eq!(
            infos.len() as u64,
            module.decoded,
            "{} declaration census changed between passes",
            module.name
        );
        assert_eq!(
            infos
                .iter()
                .filter(|info| reference_replay_skips(info))
                .count() as u64,
            module.oracle_skipped,
            "{} oracle-applicability census changed between passes",
            module.name
        );
        let (active_infos, active_to_decoded, shadowed) = reference_active_rows(&infos);

        let reconstructed = reconstruct_import_context(module, &inventory, &order_index, &states);
        let ReconstructedImportContext {
            imported: imported_context,
            closure,
            faithful: mut context_faithful,
            collisions,
        } = reconstructed;
        for (dependency, names) in &collisions {
            eprintln!(
                "kernel_reference_corpus finding: module={} direction=unscorable \
                 reason=import_context_collision dependency={} affected={} first={:?}",
                module.name,
                dependency,
                names.len(),
                names.iter().take(5).collect::<Vec<_>>()
            );
        }

        let (counts, stream_digest) = if context_faithful {
            let prep = prepare_replay_from(
                imported_context.environment.clone(),
                Some(&imported_context),
                &active_infos,
                false,
            );
            // ONE PINNED WIDTH. This census scores verdicts against the oracle; it
            // is not, and after R2 still is not, a determinism matrix. The width was
            // a size heuristic — `if prep.items.len() < 64 { 1 } else { 8 }` — under
            // which two modules of different sizes ran at DIFFERENT widths, so the
            // census was not even produced at one consistent configuration, and runs
            // not produced under comparable configurations cannot support a
            // determinism claim at all (R1 of bead `fln-corpus-thread-matrix-93te`).
            //
            // The cross-width comparison lives in
            // `present_olean_corpus_thread_matrix_compares_stream_digests`, which
            // replays the SAME reconstructed environments at every width in
            // `CORPUS_MATRIX_WIDTHS`. `CORPUS_CENSUS_WIDTH` is one of those widths, so
            // this run is that matrix's middle column rather than a fourth
            // configuration — but nothing HERE compares digests across widths, so
            // these counts remain evidence about verdict agreement only. What the
            // matrix earns is a separate, weaker-than-invariant claim, stated in the
            // CLAIM-CLASS row below and in the matrix test's own census.
            let threads = CORPUS_CENSUS_WIDTH;
            let run = check_matrix_run(&prep, threads, Budget::DEFAULT);
            (
                score_accepted_reference_module(
                    module,
                    &infos,
                    &active_infos,
                    &active_to_decoded,
                    &shadowed,
                    &prep,
                    &run,
                ),
                run.stream_digest,
            )
        } else {
            let dynamic_oracle_skips = shadowed
                .iter()
                .filter(|row| !reference_replay_skips(&infos[**row]))
                .count() as u64;
            let oracle_skipped = module.oracle_skipped + dynamic_oracle_skips;
            let counts = CorpusCounts {
                decoded: module.decoded,
                unscorable: module.decoded,
                oracle_skipped,
                subject_no_answer: module.decoded - oracle_skipped,
                ..CorpusCounts::default()
            };
            counts.assert_conservation(&module.name);
            eprintln!(
                "kernel_reference_corpus finding: module={} direction=unscorable \
                 reason=import_context_not_faithfully_representable affected={}",
                module.name, module.decoded
            );
            (
                counts,
                tagged_fixture_hash(
                    b"fln.kernel-reference-corpus.context-unavailable/1",
                    &[module.name.as_bytes()],
                ),
            )
        };
        println!(
            "kernel_reference_corpus module={} index={} decoded={} compared={} \
             disagreements={} unsoundly_permissive={} restrictive_with_carve_out={} \
             restrictive_without_carve_out={} unscorable={} oracle_skipped={} \
             subject_no_answer={} stream_digest={}",
            module.name,
            index,
            counts.decoded,
            counts.compared,
            counts.disagreements(),
            counts.unsoundly_permissive,
            counts.restrictive_with_carve_out,
            counts.restrictive_without_carve_out,
            counts.unscorable,
            counts.oracle_skipped,
            counts.subject_no_answer,
            stream_digest
        );
        total.add(&counts);
        let (context, current_merge) =
            extend_reference_fixture_environment(imported_context, &active_infos, &module.name)
                .expect("publish decoded module into non-authoritative Reference fixture context");
        if !current_merge.collisions.is_empty() {
            context_faithful = false;
            eprintln!(
                "kernel_reference_corpus finding: module={} direction=unscorable \
                 reason=current_module_context_collision affected={} first={:?}",
                module.name,
                current_merge.collisions.len(),
                current_merge.collisions.iter().take(5).collect::<Vec<_>>()
            );
        }
        states.insert(
            module.name.clone(),
            CorpusFixtureState {
                closure,
                context,
                active_infos,
                faithful: context_faithful,
            },
        );
    }
    total.assert_conservation(corpus_label);
    println!(
        "kernel_reference_corpus SUMMARY: corpus={} {} of {} decoded declarations compared, \
         {} disagreements, split by direction: unsoundly_permissive={} \
         restrictive_with_carve_out={} restrictive_without_carve_out={}; \
         unscorable={} oracle_skipped={} subject_no_answer={} modules={} \
         missing_imports={} fixture_hash={} \
         schedule_independence=not_measured_in_this_run",
        corpus_label,
        total.compared,
        total.decoded,
        total.disagreements(),
        total.unsoundly_permissive,
        total.restrictive_with_carve_out,
        total.restrictive_without_carve_out,
        total.unscorable,
        total.oracle_skipped,
        total.subject_no_answer,
        inventory.modules.len(),
        inventory.missing_imports.len(),
        inventory.fixture_hash
    );
    // The claim class that belongs to the numbers above, printed with them so it
    // cannot be dropped when they are quoted (bead `fln-8zsq`). PG-5 asks for a
    // measured invariant across {1, 8, 32}; what this run supports is weaker,
    // and D7 forbids the weaker class standing in for the stronger one.
    //
    // The cross-width matrix now EXISTS (R2 of `fln-corpus-thread-matrix-93te`) and is
    // named here so a reader of these counts can find it — but it is a different lane
    // with a different, still-not-invariant class, and it does not run per commit. The
    // row therefore points at it and states the shortfall rather than inheriting its
    // result: pointing at evidence is not the same as carrying it.
    println!(
        "kernel_reference_corpus CLAIM-CLASS: schedule_independence=not_measured_in_this_run \
         corpus_widths=one_pinned_width_no_cross_width_comparison_here \
         basis=prelude_matrix_{{1,8,32}}+kernel_purity+deterministic_merge \
         matrix_lane=present_olean_corpus_thread_matrix_compares_stream_digests \
         matrix_class=see_that_lanes_own_CLAIM-CLASS_row_it_is_not_an_invariant \
         cadence=corpus_matrix_is_on_demand_NOT_per_commit_a_documented_PG-5_shortfall \
         means=these_counts_are_NOT_evidence_of_deterministic_corpus_checking \
         bead=fln-8zsq,fln-corpus-thread-matrix-93te"
    );
    assert!(
        total.compared >= compared_floor,
        "kernel differential coverage silently stopped: {} < {} scoreable declarations",
        total.compared,
        compared_floor
    );
    assert_eq!(
        total.unsoundly_permissive, 0,
        "accepting what the Reference rejects is release-blocking; no carve-out exists"
    );
    assert_eq!(
        total.restrictive_without_carve_out, 0,
        "restrictive disagreements require repair or an explicit justified D23 row"
    );
    assert_eq!(
        total.unscorable, 0,
        "a non-answer from either side agrees with nothing"
    );
}

/// The corpus-scale `{1, 8, 32}` thread matrix (R2 of bead
/// `fln-corpus-thread-matrix-93te`) — and, just as load-bearing, the one claim a green run
/// of it is allowed to buy.
///
/// **What it does.** Every present pinned module is decoded, its PRESENT-import closure is
/// reconstructed by `reconstruct_import_context` — the same function the corpus census
/// uses, so these are the same environments — and the prepared units are replayed at every
/// width in `CORPUS_MATRIX_WIDTHS` through the same `check_matrix_run` the Prelude matrix
/// uses. The three runs go to `first_divergence_across_widths`, which names the PAIR of
/// widths, the unit index and the lead. That is R3's requirement that the assertion be
/// scoped to the site producing the digests rather than to "some equality held somewhere
/// in the run".
///
/// **No oracle is involved, deliberately.** Comparing our own stream digests across widths
/// needs no Reference verdict at all, so this lane is reachable while `fln-7odd` keeps
/// `pinned_present_olean_kernel_differential` ignored. Removing that attribute to get a
/// matrix running would have coupled the matrix half to the oracle half for no reason.
///
/// **What a green run earns, stated because the whole bead is about not overclaiming.**
/// ONE OBSERVATION: this corpus revision, this pin, this host, this build, this run. Class
/// `bounded_model`, never `invariant`. FL-INV-01 is an invariant claim and PG-5 asks for
/// {1, 8, 32} PER COMMIT; this lane is `#[ignore]`d for cost and additionally SKIPs typed
/// where the pin is absent, so it gates nothing and a SKIP produces no evidence at all.
/// The gap between one observation and the invariant is a DOCUMENTED SHORTFALL against
/// PG-5, not compliance with it, and D7 forbids the observation standing in for the
/// invariant. A lane that has not executed earns strictly nothing.
///
/// **Scope decided rather than assumed.** The comparison is PER MODULE, over each module's
/// own unit stream, because that is the unit the census scores and the unit whose
/// environment `prepare_replay_from` fixes. The per-width corpus digest in the SUMMARY is
/// a fold over those per-module digests: a summary OF the evidence, never the evidence
/// itself, which is why the comparison that fails the lane lives at the module site.
///
/// Human rows go to stderr, per the module doc's stream contract — also the only thing
/// that keeps this lane's output from corrupting an NDJSON capture if it is ever run
/// inside one. It emits no `fln.e2e.kernel-admission` rows because nothing consumes them
/// yet; wiring that up is part of what a real cadence would cost.
///
/// Run it explicitly:
///
/// `cargo test --locked -p fln-conformance --test kernel_replay \
///  present_olean_corpus_thread_matrix_compares_stream_digests -- --ignored --exact --nocapture`
#[test]
#[ignore = "cost: the whole pinned corpus replayed at three widths; on-demand lane, not per commit — a documented PG-5 shortfall (bead fln-corpus-thread-matrix-93te R4). The measured wall time is reported by the run itself, in the SUMMARY row, rather than copied here where it would rot"]
fn present_olean_corpus_thread_matrix_compares_stream_digests() {
    let rig = pin::RigRun::new(pin::PinRig::PresentOleanCorpusThreadMatrix);
    let Some(reference_lib) = reference_lib() else {
        eprintln!(
            "{}",
            rig.typed_skip()
                .expect("record the typed corpus thread-matrix skip")
        );
        return;
    };
    let started = Instant::now();
    let inventory =
        inventory_present_oleans(&reference_lib).expect("inventory every present pinned olean");
    let order = corpus_module_order(&inventory).expect("canonical present-module order");
    assert!(
        inventory.modules.len() as u64 >= PINNED_PRESENT_OLEAN_FLOOR,
        "present-module coverage floor: {} < {PINNED_PRESENT_OLEAN_FLOOR}",
        inventory.modules.len()
    );
    assert!(
        inventory.decoded >= PINNED_DECODED_DECL_FLOOR,
        "decoded-declaration coverage floor: {} < {PINNED_DECODED_DECL_FLOOR}",
        inventory.decoded
    );
    let order_index = order
        .iter()
        .enumerate()
        .map(|(index, name)| (name.clone(), index))
        .collect::<HashMap<_, _>>();

    let mut states = BTreeMap::<String, CorpusFixtureState>::new();
    let mut divergences: Vec<String> = Vec::new();
    let mut matrixed_modules = 0_u64;
    let mut matrixed_units = 0_u64;
    let mut matrixed_decls = 0_u64;
    let mut unmatrixed_modules = 0_u64;
    let mut unmatrixed_decls = 0_u64;
    let mut width_micros = [0_u128; CORPUS_MATRIX_WIDTHS.len()];
    let mut width_streams = vec![String::new(); CORPUS_MATRIX_WIDTHS.len()];

    for (index, module_name) in order.iter().enumerate() {
        let module = &inventory.modules[module_name];
        let decoded_module = decode_corpus_module(&module.path, &module.name)
            .expect("decode governed corpus module");
        let current_hash = decoded_module.olean_hash;
        let infos = decoded_module.infos;
        // The census's own two identity checks. A corpus that moved under the run would
        // make every digest below evidence about an input nobody named.
        assert_eq!(
            current_hash, module.olean_hash,
            "{} changed between inventory and replay",
            module.name
        );
        assert_eq!(
            infos.len() as u64,
            module.decoded,
            "{} declaration census changed between passes",
            module.name
        );
        let (active_infos, _, _) = reference_active_rows(&infos);
        let ReconstructedImportContext {
            imported: imported_context,
            closure,
            faithful: mut context_faithful,
            collisions,
        } = reconstruct_import_context(module, &inventory, &order_index, &states);
        for (dependency, names) in &collisions {
            eprintln!(
                "kernel_reference_corpus_matrix finding: module={} index={index} \
                 direction=unmatrixed reason=import_context_collision dependency={} \
                 affected={} first={:?}",
                module.name,
                dependency,
                names.len(),
                names.iter().take(5).collect::<Vec<_>>()
            );
        }

        if context_faithful {
            let prep = prepare_replay_from(
                imported_context.environment.clone(),
                Some(&imported_context),
                &active_infos,
                false,
            );
            let mut runs = Vec::with_capacity(CORPUS_MATRIX_WIDTHS.len());
            for (slot, &threads) in CORPUS_MATRIX_WIDTHS.iter().enumerate() {
                let run = check_matrix_run(&prep, threads, Budget::DEFAULT);
                width_micros[slot] = width_micros[slot].saturating_add(run.duration_us);
                width_streams[slot].push_str(&module.name);
                width_streams[slot].push('\u{1f}');
                width_streams[slot].push_str(&run.stream_digest);
                width_streams[slot].push('\n');
                runs.push(run);
            }
            // THE COMPARISON SITE (R3). It runs on the three runs this module just
            // produced, and its report names the diverging PAIR and the unit — never
            // "the corpus disagreed somewhere".
            //
            // A divergence is recorded and the walk continues, so a schedule-dependent
            // corpus yields every diverging module rather than a panic at the first one.
            // The assertion at the end is what fails the lane.
            let divergence = first_divergence_across_widths(&runs);
            if let Some(divergence) = &divergence {
                eprintln!(
                    "kernel_reference_corpus_matrix finding: module={} index={index} \
                     direction=schedule_dependent {divergence}",
                    module.name
                );
                divergences.push(format!("module={} {divergence}", module.name));
            }
            matrixed_modules += 1;
            matrixed_units += prep.items.len() as u64;
            matrixed_decls += module.decoded;
            let digests = runs
                .iter()
                .map(|run| format!("{}:{}", run.threads, run.stream_digest))
                .collect::<Vec<_>>()
                .join(",");
            eprintln!(
                "kernel_reference_corpus_matrix module={} index={index} decoded={} units={} \
                 widths={CORPUS_MATRIX_WIDTHS:?} digests={digests} \
                 identical_across_widths={} matrix_us={}",
                module.name,
                module.decoded,
                prep.items.len(),
                divergence.is_none(),
                runs.iter().map(|run| run.duration_us).sum::<u128>()
            );
        } else {
            unmatrixed_modules += 1;
            unmatrixed_decls += module.decoded;
            eprintln!(
                "kernel_reference_corpus_matrix finding: module={} index={index} \
                 direction=unmatrixed reason=import_context_not_faithfully_representable \
                 affected={}",
                module.name, module.decoded
            );
        }

        let (context, current_merge) =
            extend_reference_fixture_environment(imported_context, &active_infos, &module.name)
                .expect("publish decoded module into non-authoritative Reference fixture context");
        if !current_merge.collisions.is_empty() {
            context_faithful = false;
            eprintln!(
                "kernel_reference_corpus_matrix finding: module={} index={index} \
                 direction=unmatrixed reason=current_module_context_collision affected={} \
                 first={:?}",
                module.name,
                current_merge.collisions.len(),
                current_merge.collisions.iter().take(5).collect::<Vec<_>>()
            );
        }
        states.insert(
            module.name.clone(),
            CorpusFixtureState {
                closure,
                context,
                active_infos,
                faithful: context_faithful,
            },
        );
    }

    // Count conservation, in the same spirit as `CorpusCounts::assert_conservation`: every
    // decoded declaration is either inside the matrix or explicitly outside it, so no row
    // can go missing between the inventory and the comparison.
    assert_eq!(
        matrixed_decls + unmatrixed_decls,
        inventory.decoded,
        "matrix coverage lost declarations: {matrixed_decls} + {unmatrixed_decls} != {}",
        inventory.decoded
    );
    assert_eq!(
        unmatrixed_modules, 0,
        "{unmatrixed_modules} module(s) covering {unmatrixed_decls} declarations were left \
         OUT of the matrix; the observation below would then be about a subset nobody \
         named. Every present import closure is representable at this pin \
         (`present_olean_import_contexts_accept_reference_extended_duplicates` asserts \
         zero collisions), so this is a real regression, not a tolerance"
    );

    let corpus_digests = width_streams
        .iter()
        .map(|stream| {
            tagged_fixture_hash(
                b"fln.kernel-reference-corpus.matrix-stream/1",
                &[stream.as_bytes()],
            )
        })
        .collect::<Vec<_>>();
    let folds_agree = corpus_digests
        .iter()
        .all(|digest| *digest == corpus_digests[0]);
    let per_width_ms = width_micros
        .iter()
        .zip(CORPUS_MATRIX_WIDTHS)
        .map(|(micros, threads)| format!("{threads}:{}", micros / 1_000))
        .collect::<Vec<_>>()
        .join(",");
    // The class both rows carry must describe THIS run. A fixed `observed_...` token would
    // keep claiming an observation of schedule-independence in exactly the case where the
    // run REFUTED it — and the census rows print before the assertions, deliberately, so
    // that a failing run still leaves machine evidence. A row that survives the failure
    // must not survive it saying the opposite of what happened.
    let observed = if divergences.is_empty() {
        "schedule_independence=observed_once_not_an_invariant"
    } else {
        "schedule_independence=refuted_this_run_found_a_width_disagreement"
    };
    // `units` is what was actually compared; `decoded_in_matrixed_modules` is only the
    // attribution of decoded rows to modules that entered the matrix. They are reported
    // separately on purpose: a decoded row can be shadowed, unchecked or
    // ArtifactIncomplete and so never become a unit, and naming the larger number as
    // coverage would claim comparisons that never happened.
    eprintln!(
        "kernel_reference_corpus_matrix SUMMARY: modules={matrixed_modules} of {} present, \
         decoded_in_matrixed_modules={matrixed_decls} of {}, units_compared={matrixed_units}, \
         widths={CORPUS_MATRIX_WIDTHS:?}, diverging_modules={}, unmatrixed_modules={unmatrixed_modules}, \
         corpus_digests={}, folds_agree={folds_agree}, per_width_ms={per_width_ms}, \
         wall_ms={}, fixture_hash={} {observed}",
        inventory.modules.len(),
        inventory.decoded,
        divergences.len(),
        corpus_digests
            .iter()
            .zip(CORPUS_MATRIX_WIDTHS)
            .map(|(digest, threads)| format!("{threads}:{digest}"))
            .collect::<Vec<_>>()
            .join(","),
        started.elapsed().as_millis(),
        inventory.fixture_hash
    );
    // The claim class travels WITH the numbers (bead `fln-8zsq`), and separately as its
    // own row, because the numbers are what gets quoted. `wall_ms` above is the price of
    // one observation and is therefore the input to the cadence question, not decoration.
    eprintln!(
        "kernel_reference_corpus_matrix CLAIM-CLASS: {observed} \
         class=bounded_model_NOT_invariant \
         earns=one_observation_at_this_corpus_revision_this_pin_this_host_this_run \
         scope=per_module_verdict_stream_and_consumption_compared_across_{{1,8,32}} \
         cadence=on_demand_ignored_by_default_and_skips_typed_without_the_pin \
         pg5=a_PER_COMMIT_corpus_matrix_is_STILL_ABSENT_this_is_a_documented_shortfall_not_compliance \
         means=a_green_run_here_does_NOT_make_FL-INV-01_measured_over_the_corpus \
         bead=fln-corpus-thread-matrix-93te"
    );

    // THE RETAINED EVIDENCE (bead `franken_lean-p6x1`). The row is always printed, so a
    // run that nobody thought to capture still leaves its identity in the log; it is
    // written into the tree only when the operator names a path, because a test that
    // edits a tracked file on its own would be a governed-input mutation and could void
    // somebody else's lane. `observed_utc` is supplied by the caller for the same reason
    // the class is derived from the run: a value invented here could not be checked.
    let receipt = CorpusMatrixReceipt {
        bead: "fln-corpus-thread-matrix-93te".to_string(),
        pin: suite_lock_reference_pin(),
        observed_unix_s: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|since| since.as_secs())
            .unwrap_or(0),
        corpus_fixture_hash: inventory.fixture_hash.clone(),
        modules: matrixed_modules,
        decoded: matrixed_decls,
        units_compared: matrixed_units,
        widths: CORPUS_MATRIX_WIDTHS.iter().map(|w| *w as u64).collect(),
        corpus_digests: corpus_digests.clone(),
        diverging_modules: divergences.len() as u64,
        unmatrixed_modules,
        wall_ms: u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX),
        per_width_ms: width_micros
            .iter()
            .map(|micros| u64::try_from(micros / 1_000).unwrap_or(u64::MAX))
            .collect(),
        profile: if cfg!(debug_assertions) {
            "dev"
        } else {
            "release"
        }
        .to_string(),
        target: format!("{}-{}", std::env::consts::ARCH, std::env::consts::OS),
        available_parallelism: std::thread::available_parallelism()
            .map(|n| n.get() as u64)
            .unwrap_or(0),
        // The lane digests its OWN source, so the provenance cannot be forgotten by an
        // operator or mistyped by one.
        lane_source_digest_at_run: hash(
            Domain::Fixture,
            include_str!("kernel_replay.rs").as_bytes(),
        )
        .to_hex(),
        class: if divergences.is_empty() {
            "observed_once_not_an_invariant"
        } else {
            "refuted_this_run_found_a_width_disagreement"
        }
        .to_string(),
    };
    let row = receipt.to_row();
    eprintln!("kernel_reference_corpus_matrix RECEIPT: {row}");
    if let Ok(path) = std::env::var("FLN_CORPUS_MATRIX_RECEIPT") {
        let mut file = fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&path)
            .unwrap_or_else(|error| panic!("open receipt {path}: {error}"));
        writeln!(file, "{row}").unwrap_or_else(|error| panic!("append receipt {path}: {error}"));
    }

    // One direction only. A differing fold with no per-module divergence is impossible and
    // means the summary and the evidence it summarises disagree. The converse is NOT a
    // contradiction: `first_divergence_across_widths` also reports differing step and depth
    // consumption at identical digests, which the digest fold cannot see — FL-INV-01 covers
    // exact consumption, not just verdicts.
    assert!(
        folds_agree || !divergences.is_empty(),
        "the per-width corpus digest fold differs while every per-module comparison agreed; \
         the fold and the evidence it summarises cannot both be right: {corpus_digests:?}"
    );
    assert!(
        divergences.is_empty(),
        "corpus replay is schedule-DEPENDENT across widths {CORPUS_MATRIX_WIDTHS:?}: {} \
         module(s) diverged. First: {}",
        divergences.len(),
        divergences[0]
    );
    rig.executed()
        .expect("record the executed corpus thread-matrix observation");
}

#[test]
fn prelude_replays_through_the_kernel() {
    let rig = pin::RigRun::new(pin::PinRig::PreludeKernelReplay);
    let Some((bytes, infos)) = decode_prelude() else {
        eprintln!(
            "{}",
            rig.typed_skip()
                .expect("record the typed Prelude kernel-replay skip")
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
    // Shared with the corpus matrix (R2 of `fln-corpus-thread-matrix-93te`) so the two
    // scopes cannot drift apart in what they consider a divergence. Consumption equality
    // is folded in, so `identical` is exactly "no divergence found".
    let first_divergence = first_divergence_across_widths(&runs);
    let identical = first_divergence.is_none();
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
    rig.executed()
        .expect("record the executed Prelude kernel replay");
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
        ResourceReason::Heartbeats { .. } => ("inconclusive:Heartbeats".into(), usage.observed, 0),
        ResourceReason::ExecutionSteps => ("inconclusive:Steps".into(), usage.observed, 0),
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

    let rig = pin::RigRun::new(pin::PinRig::AdmissionFaultMatrix);
    let Some((bytes, infos)) = decode_prelude() else {
        eprintln!(
            "{}",
            rig.typed_skip()
                .expect("record the typed admission fault-matrix skip")
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
        // MECHANICAL ONLY (cc_2, bead franken_lean-4o3n): a `Budget` now carries
        // the calibration its depth ceiling was derived from, so there is no
        // struct-literal form. `narrowed` lowers the allowances and keeps that
        // derivation; the steps and depth asked for here are unchanged.
        let exact = budget.narrowed(s, budget.depth);
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
        let under = budget.narrowed(s - 1, budget.depth);
        let v = fln_kernel::check(&subject.env, &subject.decl, under);
        let (actual, class, _msg, steps_used, max_depth) = verdict_facts(&v);
        let ok = matches!(
            resource_exhaustion(&v),
            Some(ResourceUsage {
                reason: ResourceReason::ExecutionSteps,
                allowed,
                observed,
            }) if *allowed == under.steps
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
        let shallow = budget.narrowed(budget.steps, 2);
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
    rig.executed()
        .expect("record the executed admission fault matrix");
}

/// Both corpus censuses must keep disclosing their own claim class, and neither may
/// strengthen that class beyond what its own code produces.
///
/// **Why this is a source-level guard and not a log assertion.** Both censuses are printed
/// by `#[ignore]`d tests — the oracle differential pending `fln-7odd`, the thread matrix
/// for cost — so a lane that greps stdout observes nothing at all: not a missing
/// disclosure, just silence. Reading the source is the only check that discriminates here.
///
/// **What it is for.** AGENTS.md's recurring-defect table records `fln-8zsq` as the one
/// entry caught by *nothing*: the census disclosed its own limit in prose, and deleting
/// that prose left every gate green. A disclosure protecting a claim, with nothing
/// protecting the disclosure. This is the missing half.
///
/// **What R2 of `fln-corpus-thread-matrix-93te` changed here.** Stream digests are now
/// compared across {1, 8, 32} over the corpus, so the honest class moved from *inferred*
/// to *one observation*. It did not become an invariant: the lane is `#[ignore]`d, it SKIPs
/// typed without the pin, and PG-5 asks for {1, 8, 32} **per commit**. So the check is no
/// longer "is the word `measured` present" — it pins each region's class token to what
/// that region's code actually does, in both directions, and refuses when the code that
/// earned a token changes underneath it.
#[test]
fn corpus_census_keeps_disclosing_its_claim_class() {
    const SOURCE: &str = include_str!("kernel_replay.rs");

    /// The source of the print macro that emits `needle`, from the needle to the end of
    /// that macro call.
    ///
    /// Every assertion below is scoped to ONE row's site. A file-wide `contains` was
    /// satisfied by a *different* row while the row under test was gutted, and the planted
    /// mutant survived — the wrong-scope defect `fln-8zsq` is about, reproduced inside its
    /// own first fix.
    fn emitting_row<'a>(source: &'a str, needle: &str) -> &'a str {
        let start = source
            .find(needle)
            .unwrap_or_else(|| panic!("the census row `{needle}` must exist"));
        let rest = &source[start..];
        let end = rest
            .find("\n    );")
            .unwrap_or_else(|| panic!("`{needle}` must sit inside a print macro call"));
        &rest[..end]
    }

    /// The token following `schedule_independence=` at `start`, read to the first character
    /// that cannot be part of it.
    ///
    /// Token-exact on purpose. `contains("schedule_independence=measured")` is a PREFIX
    /// match, so it cannot tell `measured` from `measured_one_observation` — a projection
    /// used as an identity without checking it is injective, which is the defect shape this
    /// file has now hit three times.
    fn class_token(rest: &str) -> &str {
        let end = rest
            .find(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '-'))
            .unwrap_or(rest.len());
        &rest[..end]
    }

    // This guard must not be able to satisfy itself. Every needle below also occurs in this
    // function's own body, so a whole-file search would match the assertion text and stay
    // green after the census stopped disclosing anything. The search region is the file
    // strictly BEFORE this guard, which is also strictly before every other guard.
    let guard = SOURCE
        .find("fn corpus_census_keeps_disclosing_its_claim_class")
        .expect("the guard must be able to locate its own definition");
    let census = &SOURCE[..guard];
    assert!(
        census.len() > 100_000,
        "search region collapsed to {} bytes, so the self-exclusion split is wrong and \
         these assertions would be checking almost nothing",
        census.len()
    );
    // Every probe about what the code DOES runs over `code`, with comments removed. The
    // first version of this guard read raw source and failed on the oracle census — whose
    // comment NAMES `CORPUS_MATRIX_WIDTHS` while its code runs one width. Prose describing
    // a property is not the property; a guard that cannot tell them apart is the same
    // self-match that has now bitten this file four times. `census` itself is used only
    // where the prose IS the subject, which is assertion 3.
    let code = comment_free(census);
    let code = code.as_str();

    // The two censuses make two different claims from two different runs, so the regions
    // below are per test, and the CODE regions deliberately start at `fn` rather than at
    // the doc comment: prose that *describes* a matrix would otherwise satisfy a probe for
    // one. A guard's search space must exclude every text that merely claims the property.
    let oracle_start = code
        .find("fn pinned_present_olean_kernel_differential")
        .expect("the corpus differential must exist");
    let matrix_start = code
        .find("fn present_olean_corpus_thread_matrix_compares_stream_digests")
        .expect(
            "the corpus thread matrix must exist (R2 of fln-corpus-thread-matrix-93te); the \
             census rows below name it as the lane that measures what they do not",
        );
    let matrix_item_start = code[..matrix_start]
        .rfind("\n\n")
        .map(|offset| offset + 2)
        .expect("the matrix test must be preceded by another item");
    let matrix_end = code[matrix_start..]
        .find("fn prelude_replays_through_the_kernel")
        .map(|offset| matrix_start + offset)
        .expect("the Prelude replay must follow the corpus thread matrix");
    assert!(
        oracle_start < matrix_item_start,
        "the region split assumes the oracle census precedes the thread matrix"
    );
    let oracle_code = &code[oracle_start..matrix_item_start];
    let matrix_code = &code[matrix_start..matrix_end];

    // 1. Each SUMMARY row carries its class INLINE, because the numbers are what gets
    //    quoted out of this file and a standalone CLAIM-CLASS row does not travel with
    //    them.
    //
    //    The oracle census's class is fixed — its run measures nothing about schedules
    //    either way. The matrix's is not: it interpolates `{observed}`, whose two branches
    //    are checked below, because the census rows print BEFORE the assertions so a
    //    failing run still leaves machine evidence. A fixed token would have that surviving
    //    row claim an observation of schedule-independence in exactly the run that refuted
    //    it.
    for (row, token) in [
        (
            "kernel_reference_corpus SUMMARY:",
            "schedule_independence=not_measured_in_this_run",
        ),
        ("kernel_reference_corpus_matrix SUMMARY:", "{observed}"),
    ] {
        assert!(
            emitting_row(code, row).contains(token),
            "`{row}` no longer carries `{token}` inline, so its counts can be quoted bare \
             and would read as evidence of deterministic corpus checking (bead fln-8zsq)"
        );
    }
    for branch in [
        "schedule_independence=observed_once_not_an_invariant",
        "schedule_independence=refuted_this_run_found_a_width_disagreement",
    ] {
        assert!(
            matrix_code.contains(branch),
            "the matrix census lost the `{branch}` branch of its class binding. Both must \
             exist, or a run that found a width disagreement reports the class of one that \
             did not — in a row that prints before the assertion precisely so it survives \
             the failure"
        );
    }

    // 2. Each CLAIM-CLASS row keeps naming its basis, its limit, and the cadence. Losing
    //    `means=` is the worst case: the row would still look like evidence.
    let oracle_claim = emitting_row(code, "kernel_reference_corpus CLAIM-CLASS:");
    for needle in [
        "basis=prelude_matrix_",
        "means=these_counts_are_NOT_evidence_of_deterministic_corpus_checking",
        "shortfall",
        // The join: this row points at the lane that measures what it cannot, so it must
        // name that lane exactly. A rename that did not reach here would leave a pointer
        // to nothing, which is the failure AGENTS.md item 7 keeps recording.
        "matrix_lane=present_olean_corpus_thread_matrix_compares_stream_digests",
    ] {
        assert!(
            oracle_claim.contains(needle),
            "the oracle census CLAIM-CLASS row lost `{needle}`, so it no longer states what \
             its numbers are not evidence of, or where the missing evidence lives (beads \
             fln-8zsq, fln-corpus-thread-matrix-93te)"
        );
    }
    let matrix_claim = emitting_row(code, "kernel_reference_corpus_matrix CLAIM-CLASS:");
    for needle in [
        "class=bounded_model_NOT_invariant",
        "earns=one_observation",
        "means=a_green_run_here_does_NOT_make_FL-INV-01_measured_over_the_corpus",
        "shortfall",
    ] {
        assert!(
            matrix_claim.contains(needle),
            "the matrix census CLAIM-CLASS row lost `{needle}`; a green matrix run is one \
             observation at one revision, pin and host, and D7 forbids it standing in for \
             the invariant PG-5 asks for (bead fln-corpus-thread-matrix-93te R5)"
        );
    }

    // 3. The module doc must keep scoping the PER-COMMIT matrix. Before fln-8zsq it said
    //    the matrix "PROVES it byte-equal at every width" with no input named, sitting
    //    above both tests, which is how the corpus got read into it.
    assert!(
        census.contains("The per-commit matrix does not cover the corpus"),
        "the module doc no longer scopes the per-commit {{1, 8, 32}} matrix to the Prelude, \
         so it reads as covering the corpus too (beads fln-8zsq, \
         fln-corpus-thread-matrix-93te)"
    );

    // 4. The class may not silently strengthen — checked as an exact token against a
    //    declared allowance, in BOTH directions, so the allowance shrinks when a row is
    //    repaired instead of accumulating dead permissions.
    const PERMITTED_CLASSES: [&str; 3] = [
        "not_measured_in_this_run",
        "observed_once_not_an_invariant",
        "refuted_this_run_found_a_width_disagreement",
    ];
    let mut cursor = code;
    while let Some(offset) = cursor.find("schedule_independence=") {
        let rest = &cursor[offset + "schedule_independence=".len()..];
        let token = class_token(rest);
        assert!(
            PERMITTED_CLASSES.contains(&token),
            "a census claims schedule_independence={token}, which is not one of the classes \
             this file's code earns {PERMITTED_CLASSES:?}. The corpus is checked at one \
             pinned width by the oracle census and compared across {{1, 8, 32}} by an \
             on-demand lane that gates nothing, so nothing here earns an invariant. If the \
             evidence really changed, change this allowance deliberately (D7, PG-5, beads \
             fln-8zsq, fln-corpus-thread-matrix-93te)"
        );
        cursor = rest;
    }
    for permitted in PERMITTED_CLASSES {
        assert!(
            code.contains(&format!("schedule_independence={permitted}")),
            "the allowance permits `{permitted}` but nothing states it; a permission that \
             outlives the row it was written for is how a strengthened claim slips through"
        );
    }

    // 5. Each class token must be earned by the code in its own region. This is assertion 4
    //    in the direction that matters: a token is a claim ABOUT code, so the guard checks
    //    the code. The oracle census scores at exactly one width and must keep saying so;
    //    the matrix census may claim its observation only while it really replays every
    //    width over one prepared module and compares the runs.
    assert!(
        oracle_code.contains("let threads = CORPUS_CENSUS_WIDTH;"),
        "the oracle census no longer runs at the single pinned width its CLAIM-CLASS row \
         describes"
    );
    assert!(
        !oracle_code.contains("CORPUS_MATRIX_WIDTHS"),
        "the oracle census now runs a matrix of its own, so `not_measured_in_this_run` has \
         become false in the understating direction; re-derive its class rather than \
         leaving a stale one"
    );
    for needle in [
        "for (slot, &threads) in CORPUS_MATRIX_WIDTHS.iter().enumerate()",
        "check_matrix_run(&prep, threads, Budget::DEFAULT)",
        "first_divergence_across_widths(&runs)",
    ] {
        assert!(
            matrix_code.contains(needle),
            "the corpus matrix lost `{needle}`, so its `observed_once_not_an_invariant` \
             class is unearned: nothing compares stream digests across widths any more \
             (beads fln-8zsq, fln-corpus-thread-matrix-93te, D7, PG-5)"
        );
    }
}

/// `source` with comment text removed, for probes that ask what the code DOES.
///
/// Defined between the two source-reading guards so it sits outside both of their search
/// regions: a helper they both read would otherwise be production text to one of them.
///
/// **Why it exists.** A comment that *describes* a property satisfies a raw-source probe
/// for that property. The oracle census's own comment names `CORPUS_MATRIX_WIDTHS` while
/// its code runs one width, and the corpus matrix's doc comment writes `#[ignore]` while
/// explaining the attribute — so a probe for either would have read prose as code, in the
/// direction that reports evidence which is not there. That is the fourth self-match in
/// this file's guards; the search space must exclude every text that merely claims the
/// property.
///
/// Line comments and doc comments only. Nothing in these regions uses block comments, and
/// one appearing here would be a reason to extend this rather than to trust it.
fn comment_free(source: &str) -> String {
    source
        .lines()
        .map(|line| {
            if line.trim_start().starts_with("//") {
                ""
            } else {
                line.split(" // ").next().unwrap_or(line)
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// The `{1, 8, 32}` determinism claim must name its scope everywhere it appears, for as
/// long as the corpus-scale matrix is not the per-commit gate PG-5 names.
///
/// `fln-8zsq` scoped the claim inside this file. It stayed unscoped in AGENTS.md, README
/// and the plan, which is the same defect one level up: the claim is repository-wide and
/// the enforcement is Prelude-only, and no reader of those documents could tell. This
/// test is the join between the two artifacts, which is exactly where this project keeps
/// finding the gap.
///
/// **What R2 changed, and the trap it opened.** The corpus matrix now exists, so the old
/// probe — "does a corpus matrix loop exist?" — would have stood this guard down the moment
/// the code landed, leaving the documents free to state the claim bare. That is calibrated
/// to the wrong signal: per R5 of `fln-corpus-thread-matrix-93te` a lane that has not run
/// earns NOTHING and a lane that runs on demand earns one observation, so source existing
/// is not evidence of anything. The probe now asks whether the matrix GATES, and the
/// qualifier stays required while it does not.
///
/// It also checks the direction nothing watched before: a document may no longer say the
/// corpus matrix is unbuilt, because it is built. A stale qualifier is a false statement
/// too, and catching it must not depend on someone remembering.
#[test]
fn the_thread_matrix_claim_is_scoped_wherever_it_appears() {
    const SOURCE: &str = include_str!("kernel_replay.rs");
    // The probe region must exclude EVERY guard body, not merely this one. The needles
    // below also appear inside `corpus_census_keeps_disclosing_its_claim_class`, so a
    // region that stopped at this function would match a *test's* text and report
    // production properties that had been deleted — the self-match that has now bitten
    // three times here. Cutting at the FIRST guard leaves production code only.
    let production_end = SOURCE
        .find("fn corpus_census_keeps_disclosing_its_claim_class")
        .expect("the first source-reading guard marks the end of production code");
    // Comments removed for the same reason `comment_free` exists: the matrix test's doc
    // comment writes `#[ignore]` while explaining the attribute, so a raw-source probe for
    // the attribute would keep reporting the lane gated after someone removed it — a false
    // negative in exactly the direction that widens a claim.
    let production = comment_free(&SOURCE[..production_end]);
    let production = production.as_str();

    assert!(
        production.contains("for threads in [1usize, 8, 32]"),
        "the Prelude thread matrix disappeared; the claim would then have no support at \
         any scope"
    );
    // The widths the documents name must be the widths the code runs. Without this the
    // array could move to [1, 4, 32] while every `{1, 8, 32}` line below stayed green —
    // a claim and the thing that produces it, unjoined, which is AGENTS.md item 7 exactly.
    assert!(
        production.contains("const CORPUS_MATRIX_WIDTHS: [usize; 3] = [1, 8, 32];"),
        "the corpus matrix no longer runs the widths PG-5 names and the documents claim; \
         the {{1, 8, 32}} lines below would then describe a matrix that does not exist"
    );

    // Two facts, derived separately because they license different things: whether a
    // corpus matrix EXISTS, and whether it GATES anything. Conflating them is what would
    // have let landing R2 widen the documents' claim with nothing objecting.
    let matrix_start =
        production.find("fn present_olean_corpus_thread_matrix_compares_stream_digests");
    assert!(
        matrix_start.is_some(),
        "the corpus thread matrix disappeared (R2 of fln-corpus-thread-matrix-93te). If \
         that was deliberate, the documents must go back to saying the corpus-scale matrix \
         does not exist, and this guard must be re-derived rather than deleted"
    );
    let matrix_start = matrix_start.expect("checked immediately above");
    let matrix_item_start = production[..matrix_start]
        .rfind("\n\n")
        .map(|offset| offset + 2)
        .expect("the matrix test must be preceded by another item");
    let matrix_gates = !production[matrix_item_start..matrix_start].contains("#[ignore");
    assert!(
        !matrix_gates,
        "the corpus matrix is no longer `#[ignore]`d. That is progress and it is NOT by \
         itself the per-commit gate PG-5 names: the lane still SKIPs typed on any host \
         without the pin, so a green `cargo test` there proves nothing about the corpus. \
         Re-derive this guard and the class the documents may state, deliberately, rather \
         than letting a removed attribute widen a claim (R5 of \
         fln-corpus-thread-matrix-93te)"
    );

    let repo = fln_conformance::checked_workspace_root!();
    // Any of these makes the line honest: it names the per-commit matrix's scope, the class
    // one on-demand run earns, or the cadence gap. `unbuilt` and `inferred` used to be in
    // this set and were removed with R2 — they describe a world that no longer exists, and
    // a qualifier that has gone stale stops being a qualifier.
    const QUALIFIERS: [&str; 7] = [
        "Prelude",
        "prelude",
        "observation",
        "observed",
        "shortfall",
        "on demand",
        "93te",
    ];
    // A document may not still describe the corpus matrix as missing. Scoped to lines that
    // mention a matrix so ordinary uses of these words elsewhere are not swept in.
    const STALE: [&str; 4] = ["unbuilt", "does not exist", "is not built", "not built yet"];
    // R4 asks for the cadence STATED WHERE THE CLAIM IS MADE, so this is checked per claim
    // site, not per document. The first version checked per document and a planted mutant
    // survived it: stripping the cadence from the B4 bullet left the reader of that bullet
    // with a bare per-commit claim, while a paragraph 340 lines away kept the document
    // green. Same wrong-scope shape as fln-8zsq's first guard, one artifact up.
    // Both spellings, because `on-demand` does not contain `on demand` and the mutant that
    // taught me the first lesson also slipped past on the hyphen.
    const CADENCE: [&str; 3] = ["shortfall", "on demand", "on-demand"];
    let mut checked = 0usize;
    for doc in ["AGENTS.md", "README.md"] {
        let text = fs::read_to_string(repo.join(doc))
            .unwrap_or_else(|error| panic!("{doc} must be readable: {error}"));
        for (index, line) in text.lines().enumerate() {
            if line.contains("matrix") {
                for stale in STALE {
                    assert!(
                        !line.contains(stale),
                        "{doc}:{} still describes the corpus-scale matrix as missing, but it \
                         exists and has been run (R2 of fln-corpus-thread-matrix-93te). A \
                         stale qualifier is a false statement in the other direction:\n  {line}",
                        index + 1
                    );
                }
            }
            if !line.contains("{1, 8, 32}") {
                continue;
            }
            checked += 1;
            assert!(
                QUALIFIERS.iter().any(|word| line.contains(word)),
                "{doc}:{} states the {{1, 8, 32}} determinism claim without naming its \
                 scope, while the per-commit matrix's input is the Prelude and the \
                 corpus-scale matrix is an on-demand lane that gates nothing. A reader \
                 takes this as covering the corpus per commit (beads fln-8zsq, \
                 fln-corpus-thread-matrix-93te):\n  {line}",
                index + 1
            );
            assert!(
                CADENCE.iter().any(|word| line.contains(word)),
                "{doc}:{} states the {{1, 8, 32}} claim without naming the corpus lane's \
                 cadence. PG-5 asks for {{1, 8, 32}} PER COMMIT; the corpus lane runs on \
                 demand, which is a DOCUMENTED SHORTFALL against that gate rather than \
                 compliance with it, and a shortfall stated somewhere else in the file is \
                 not stated where this claim is read (R4 of \
                 fln-corpus-thread-matrix-93te):\n  {line}",
                index + 1
            );
        }
    }
    assert!(
        checked >= 4,
        "only {checked} determinism claim lines found across AGENTS.md and README.md; the \
         scan is looking in the wrong place and would pass over a bare claim"
    );
}

/// The PG-5 waiver expires when the Reference pin moves, and this is what notices
/// (bead `franken_lean-p6x1`).
///
/// **The decision this encodes, priced.** PG-5 asks for {1, 8, 32} per commit. The corpus
/// lane costs 1,926,656 ms — 32.1 minutes — measured, on a 64-way host, and CI installs no
/// Reference toolchain at all (`.github/workflows/ci.yml` says Reference-drift detection
/// "belongs in a scheduled job that actually installs the toolchain"; no such job exists).
/// So per-commit is not available, and the honest instrument is a waiver rather than a
/// cadence nobody dispatches.
///
/// **Why the expiry is a correspondence and not a date.** A waiver whose expiry nothing
/// checks is the recurring defect in a compliance costume. Three candidate triggers were
/// priced:
///
/// - *a calendar* — nothing in this repository gates on the wall clock, and a gate that
///   reads it answers differently for identical inputs, which contradicts FL-INV-01 on the
///   way to enforcing it. There is also no scheduled runner to lapse against.
/// - *the invalidating cone* (`fln-kernel`, `fln-env`, `fln-core`, `fln-hash`) — 148
///   commits in seven days. A red there fires several times a day and clears only by
///   paying 32 minutes; everyone would learn to ignore it. That is a ritual, and it is
///   also the honest reason this claim is `bounded_model`.
/// - *the Reference pin* — moved once in the project's life, by a reviewed ceremony. Rare,
///   deterministic, and its firing is exactly the moment the observation stops being about
///   the corpus in the tree.
///
/// The pin wins, and the binding is structural rather than declared: the receipt lives at
/// `evidence/corpus_thread_matrix/<pin>.jsonl`, so advancing `SUITE.lock` makes the file
/// the guard looks for cease to exist. No field to update, nothing to remember.
///
/// **When this fires, the reader has two actions and both are honest** — re-run the lane
/// (the message prints the command and what it cost last time) or delete the observation
/// sentences and let the claim fall back to inferred. The second is cheap and legitimate,
/// which is what keeps the red from being extortion.
///
/// **The re-run is NOT a unilateral action, and until 2026-07-27 nothing in this repository
/// said so** — the failure message handed a fresh pane a ready-to-paste command for a
/// ~32-minute pin-dependent lane on a host every pane shares, and the only place the
/// requirement existed was an orchestrator broadcast, which dies at the next rotation. The
/// message now carries it. Recorded here because it is the second instance in one day of a
/// rule living somewhere no fresh pane reads (the first was `f90ae35f`, a manifest rule that
/// existed only in a broadcast; before that, `02da1b62`, a rule living in two bead comments).
#[test]
fn the_corpus_matrix_observation_is_retained_and_bound_to_the_current_pin() {
    let pin = suite_lock_reference_pin();
    let path = corpus_matrix_receipt_path(&pin);
    let text = fs::read_to_string(&path).unwrap_or_else(|error| {
        panic!(
            "THE PG-5 WAIVER HAS EXPIRED. SUITE.lock now pins the Reference at {pin}, and no \
             corpus thread-matrix receipt exists for it ({}: {error}). Any observation on \
             file was of a different Reference, so the sentences in AGENTS.md and README \
             that describe it no longer describe this tree.\n\
             \n\
             Two ways to clear this, both honest — and (1) IS NOT YOURS TO LAUNCH \
             UNILATERALLY. It is a ~32-minute run that requires the Reference pin, on a host \
             every pane shares, so it goes through whoever sequences the swarm. Option (2) \
             needs no permission and is the reason this red is never extortion.\n\
             \n\
             (1) Re-run the lane at the new pin and commit the receipt it appends:\n\
             \x20   FLN_CORPUS_MATRIX_RECEIPT={} \\\n\
             \x20     cargo test --locked -p fln-conformance --test kernel_replay \\\n\
             \x20     present_olean_corpus_thread_matrix_compares_stream_digests \\\n\
             \x20     -- --ignored --exact --nocapture\n\
             \x20   It cost 1,926,656 ms (32.1 min) at v4.32.0 on a 64-way host; the width-1 \
             column is three quarters of that.\n\
             (2) Weaken the claim instead: remove the observation sentences from AGENTS.md \
             and README and let corpus schedule-independence go back to INFERRED. This is \
             cheaper than (1) and is a legitimate outcome — the claim is allowed to shrink.\n\
             \n\
             Deleting this test is not a third option: it is the only thing joining those \
             sentences to a run (bead franken_lean-p6x1).",
            path.display(),
            path.display(),
        )
    });

    let rows = text
        .lines()
        .filter(|line| !line.trim().is_empty())
        .collect::<Vec<_>>();
    assert!(
        !rows.is_empty(),
        "{} exists but holds no rows. An empty receipt is not a lighter claim than a \
         missing one; it is the same claim with the evidence removed",
        path.display()
    );
    let receipts = rows
        .iter()
        .enumerate()
        .map(|(index, row)| {
            CorpusMatrixReceipt::from_row(row)
                .unwrap_or_else(|error| panic!("{}:{}: {error}", path.display(), index + 1))
        })
        .collect::<Vec<_>>();

    for (index, receipt) in receipts.iter().enumerate() {
        if let Err(reason) = receipt.validate(&pin) {
            panic!("{}:{}: {reason}", path.display(), index + 1);
        }
    }

    // The claim must be re-derived when the evidence GROWS, not only when it decays. One
    // row is one observation; several are repeated observations over one corpus revision,
    // which is a different (still not invariant) class. Understating is a defect too.
    //
    // The join is an exact count, not a phrase. The first version of this check looked for
    // wordings like "run once" and "one observation", and a planted mutant walked straight
    // through it: "one recorded observation" contains neither string while saying exactly
    // the thing the check meant to catch. Prose heuristics fail open. Both documents must
    // instead carry the literal count, so the only way to add a row without re-deriving the
    // claim is to edit two documents that will not agree with the file.
    // THE DATE IS PART OF THE MARKER, AND IT IS NOT THE CALENDAR TRIGGER THIS TEST'S OWN
    // DOC-COMMENT REJECTS ABOVE. Read the distinction before changing it: the value below is
    // derived from `observed_unix_s` IN THE RECEIPT, so identical inputs give an identical
    // verdict and nothing here reads the wall clock. This can never expire on age — it fails
    // only when the documents and the receipt disagree about WHEN the observation happened.
    //
    // Why it is needed at all (bead `franken_lean-p6x1`): the count alone cannot distinguish
    // an observation made this morning from one made a year ago, and the waiver expires on
    // PIN MOVEMENT ONLY, so a single observation stands indefinitely while `SUITE.lock` sits
    // still. A reader was told how MUCH evidence exists and never how OLD it is. Measured at
    // `ccb1ca46`: `observed_unix_s` was written by the producer, serialized, parsed and
    // round-tripped — and asserted on by nothing. The one datum that could separate a run
    // that HAPPENED from a row that was FILED was consumed by no check in the repository.
    //
    // A freshness BOUND was considered and deliberately rejected: the only way to clear one
    // is a 32-minute run needing a Reference pin CI does not install, so it would redden
    // forever and be bypassed. Disclosing the date is the honest half — it makes staleness
    // visible to a reader without making it a wall.
    let repo = fln_conformance::checked_workspace_root!();
    let marker = corpus_matrix_marker(&receipts);
    for doc in ["AGENTS.md", "README.md"] {
        let doc_text = fs::read_to_string(repo.join(doc))
            .unwrap_or_else(|error| panic!("{doc} must be readable: {error}"));
        assert!(
            doc_text.contains(&marker),
            "{doc} does not carry `{marker}`, but the retained receipt at {} holds {} \
             observation(s), the most recent taken on {}. The documents and the evidence file \
             disagree about how much evidence exists or when it was taken. The count is the \
             difference between one observation (bounded_model) and a kept cadence \
             (statistical) — neither is the invariant PG-5 asks for — and the date is the \
             difference between an observation and an observation a reader can judge the age \
             of. Update both where the claim is READ, not only here (D7, bead \
             franken_lean-p6x1)",
            path.display(),
            receipts.len(),
            utc_date_from_unix_seconds(latest_observation(&receipts))
        );
    }
}

/// The exact string both documents must carry, derived from the receipts and nothing else.
///
/// A function rather than an inline `format!` because of a planted mutant that SURVIVED the
/// inline version: replacing the derived date with the literal `2026-07-26` kept the guard
/// green, since the committed receipt's instant *is* that date. The guard could not tell
/// "derives the date" from "hardcodes today's answer" — vacuity of exactly the shape
/// `fln-8zsq` records, where a check is satisfied by the thing it was meant to verify.
///
/// Pulling it out makes the derivation reachable from a test that supplies a DIFFERENT
/// instant, so a hardcoded date now disagrees with a receipt that says otherwise.
fn corpus_matrix_marker(receipts: &[CorpusMatrixReceipt]) -> String {
    format!(
        "observations recorded: {}, latest observed {}",
        receipts.len(),
        utc_date_from_unix_seconds(latest_observation(receipts))
    )
}

/// The most recent observation instant across the retained rows.
///
/// `max` rather than "the last row": row order is the append order of the lane, and a
/// reader judging staleness wants the newest evidence regardless of how the file was built.
fn latest_observation(receipts: &[CorpusMatrixReceipt]) -> u64 {
    receipts
        .iter()
        .map(|receipt| receipt.observed_unix_s)
        .max()
        .unwrap_or(0)
}

/// The marker tracks the receipts it is derived from, at instants other than today's.
///
/// This is the anti-vacuity half of the date binding, and it exists because a mutant that
/// hardcoded the committed receipt's own date survived the retention guard. Every case below
/// uses an instant the committed receipt does NOT carry, so an implementation that returns a
/// constant fails here no matter which constant it picks.
#[test]
fn the_corpus_matrix_marker_is_derived_from_the_receipts_it_describes() {
    // The committed row, varied in ONE field, following this file's existing idiom
    // (`a_receipt_that_compared_nothing_is_refused`) rather than a second hand-built fixture
    // that could drift from the real shape.
    let pin = suite_lock_reference_pin();
    let path = corpus_matrix_receipt_path(&pin);
    let text = fs::read_to_string(&path).expect("the retained receipt must be readable");
    let real = text
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(CorpusMatrixReceipt::from_row)
        .next()
        .expect("the retained receipt must hold at least one row")
        .expect("the committed row must parse");
    let at = |unix_s: u64| CorpusMatrixReceipt {
        observed_unix_s: unix_s,
        ..real.clone()
    };

    // One row, an instant that is not the committed one.
    assert_eq!(
        corpus_matrix_marker(&[at(1_709_164_800)]),
        "observations recorded: 1, latest observed 2024-02-29"
    );

    // The count moves with the row set, and the date follows the NEWEST row rather than the
    // last one appended — so the SAME two instants in either order date the claim
    // identically. Both expectations are deliberately the same string: that equality IS the
    // property, and asserting the two orderings separately is what would catch a
    // `.last()` standing in for a `.max()`.
    //
    // (Written the other way round first, expecting the later ordering to win, and the test
    // caught it: 2024-02-29 is the max regardless of position. The function was right and the
    // expectation was wrong, which is the correct direction for that mistake to be found in.)
    assert_eq!(
        corpus_matrix_marker(&[at(1_709_164_800), at(1_583_020_800)]),
        "observations recorded: 2, latest observed 2024-02-29"
    );
    assert_eq!(
        corpus_matrix_marker(&[at(1_583_020_800), at(1_709_164_800)]),
        "observations recorded: 2, latest observed 2024-02-29"
    );

    // And it must NOT be the committed receipt's date unless the receipts say so. Stated as
    // its own assertion because that is the precise mutant this test was added to kill.
    assert_ne!(
        corpus_matrix_marker(&[at(1_709_164_800)]),
        corpus_matrix_marker(&[at(1_785_035_078)]),
        "the marker is insensitive to the observation instant, so it is not deriving it"
    );
}

/// The UTC calendar date of a Unix instant, as `YYYY-MM-DD`.
///
/// Hand-rolled because D1 closes the dependency universe and there is no date crate in it —
/// `chrono` and `time` are both outside the allowlist, and this is the whole reason the
/// receipt carried a bare `u64` that nothing rendered.
///
/// This is Howard Hinnant's `civil_from_days`, shifting the epoch to 0000-03-01 so that the
/// leap day lands at the END of the internal year and every month length becomes a linear
/// function. Pure integer arithmetic, no clock read, no table.
///
/// **Verified against an independent implementation before being trusted**, because a date
/// routine that is wrong only at boundaries would put a wrong date into two documents and
/// then hold them to it forever — the marker binds the documents to THIS function's output,
/// so nothing downstream could notice the skew. `the_utc_date_derivation_matches_known_
/// calendar_dates` pins the boundary cases; the sweep behind them compared 30,000 random
/// instants against a reference and found zero disagreements.
///
/// **One mutant here is EQUIVALENT and cannot be killed — do not add an assertion for it.**
/// Changing the `/ 146_096` correction to `/ 146_095` survives, and the reason is arithmetic
/// rather than a gap in the table: the two divisors differ only at `day_of_era == 146_095`,
/// where the numerator moves from 145_998 to 145_997 and both floor to 399 on division by
/// 365. Checked exhaustively over all 146_097 day-of-era values: **0 differ**. The three
/// leap-rule mutations that ARE observable — `1_460`, `36_524` and the `year_of_era / 100`
/// correction — are each killed by the table, the second at only three days per era.
fn utc_date_from_unix_seconds(unix_s: u64) -> String {
    let days = (unix_s / 86_400) as i64;
    let z = days + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let day_of_era = z - era * 146_097;
    let year_of_era =
        (day_of_era - day_of_era / 1_460 + day_of_era / 36_524 - day_of_era / 146_096) / 365;
    let year = year_of_era + era * 400;
    let day_of_year = day_of_era - (365 * year_of_era + year_of_era / 4 - year_of_era / 100);
    let shifted_month = (5 * day_of_year + 2) / 153;
    let day = day_of_year - (153 * shifted_month + 2) / 5 + 1;
    let month = if shifted_month < 10 {
        shifted_month + 3
    } else {
        shifted_month - 9
    };
    let year = if month <= 2 { year + 1 } else { year };
    format!("{year:04}-{month:02}-{day:02}")
}

/// The date derivation is pinned at the cases a hand-rolled calendar gets wrong.
///
/// Leap years, the century rule, the 400-year exception, and the day boundary either side of
/// midnight — plus the receipt's own committed instant, so this test names the value the two
/// documents are actually held to. A generic "it returns a string" test would pass against
/// an implementation that is wrong every February.
#[test]
fn the_utc_date_derivation_matches_known_calendar_dates() {
    for (unix_s, expected) in [
        (0_u64, "1970-01-01"),
        (86_399, "1970-01-01"),
        (86_400, "1970-01-02"),
        // The receipt committed for the v4.32.0 pin. If this row ever disagrees, the marker
        // in AGENTS.md and README is wrong and this is the test that says so first.
        (1_785_035_078, "2026-07-26"),
        (951_782_400, "2000-02-29"),   // divisible by 400: IS a leap year
        (1_078_012_800, "2004-02-29"), // ordinary leap year
        (1_709_164_800, "2024-02-29"),
        (1_583_020_800, "2020-03-01"), // the day after, where an off-by-one lands
        (4_107_542_400, "2100-03-01"), // divisible by 100, NOT 400: not a leap year
        (2_147_483_647, "2038-01-19"), // the 32-bit cliff, which this must outlive
        // THE ERA BOUNDARY, and these three rows were added because a planted mutant
        // survived without them. The algorithm shifts the epoch to 0000-03-01 so each
        // 400-year era spans day_of_era 0..=146096; the `/ 146_096` term corrects ONLY the
        // final day of an era. Changing it to `/ 146_095` therefore misdates exactly one day
        // in four centuries — 2000-02-28 — and every case above still passed. A boundary
        // table that omits the boundary is a table that agrees with the bug.
        (951_696_000, "2000-02-28"), // day_of_era 146_095: the survivor's one day
        (951_868_800, "2000-03-01"), // day_of_era 0: the first day of the next era
        (13_574_563_200, "2400-02-29"), // the next era's leap day, past the 32-bit range
    ] {
        assert_eq!(
            utc_date_from_unix_seconds(unix_s),
            expected,
            "UTC date derivation disagrees at {unix_s}"
        );
    }
}

/// The receipt format is checked against the committed receipt, not only against fixtures.
///
/// `from_row` re-serializes what it read and refuses on any difference, so this exercises
/// the real bytes on disk through the real serializer. A fixture-only test would prove the
/// pair is self-consistent while the committed file said something else entirely — the
/// join between an artifact and the code that claims to read it.
#[test]
fn the_corpus_matrix_receipt_round_trips_through_its_own_serializer() {
    let pin = suite_lock_reference_pin();
    let path = corpus_matrix_receipt_path(&pin);
    let text = fs::read_to_string(&path).expect("the retained receipt must be readable");
    for (index, row) in text
        .lines()
        .filter(|line| !line.trim().is_empty())
        .enumerate()
    {
        let receipt = CorpusMatrixReceipt::from_row(row)
            .unwrap_or_else(|error| panic!("{}:{}: {error}", path.display(), index + 1));
        assert_eq!(receipt.to_row(), row, "canonical round trip");
    }

    // A planted malformation must be refused rather than read past. Note what this can and
    // cannot see: a row whose CONTENT was altered still round-trips, because it is a
    // well-formed row saying something false. Content is the guard's job above (digests all
    // equal, diverging_modules zero, pin matches the path); format is this one's. Two
    // checks, and neither pretends to be the other.
    let sample = text
        .lines()
        .find(|line| !line.trim().is_empty())
        .expect("at least one row");
    for (mutation, damaged) in [
        ("schema moved", sample.replace("receipt/1", "receipt/2")),
        (
            "field renamed away",
            sample.replacen("\"modules\":", "\"module_count\":", 1),
        ),
        (
            "one byte of whitespace",
            sample.replacen("{\"schema\"", "{ \"schema\"", 1),
        ),
    ] {
        assert!(
            CorpusMatrixReceipt::from_row(&damaged).is_err(),
            "a receipt with `{mutation}` was accepted; the reader must refuse what it cannot \
             reproduce"
        );
    }
}

/// A row that compared nothing must not stand as the observation (bead `franken_lean-p6x1`).
///
/// **The mutant this exists for, and it was live.** Measured at `2ebe03e0`, with both
/// controls: the committed receipt passed the retention guard, a wrong-pin row failed it,
/// and a row recording `modules: 0, decoded: 0, units_compared: 0, corpus_digests: []`
/// **passed**. Every check the guard had was satisfiable without comparing anything —
/// `diverging_modules: 0` because nothing was compared, and "every width agreed" vacuously
/// because `all()` over an empty list is true. That row would have been the standing
/// evidence for the PG-5 waiver and for the corpus sentences in AGENTS.md and README.
///
/// It is `bkw6`'s empty-referent shape appearing inside a mechanism built to hold a claim to
/// its evidence: the far end existed and was addressable, so every technique that compares a
/// claim against its evidence was satisfied — while the evidence asserted nothing. The move
/// that finds it is `bkw6`'s: bind the claim to the **cardinality** of what it asserts.
///
/// The mutants run against `validate`, the same function the retention guard runs, because a
/// second copy of the rules written for this test could drift from the one that gates.
#[test]
fn a_receipt_that_compared_nothing_is_refused() {
    let pin = suite_lock_reference_pin();
    let path = corpus_matrix_receipt_path(&pin);
    let text = fs::read_to_string(&path).expect("the retained receipt must be readable");
    let real = text
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(CorpusMatrixReceipt::from_row)
        .next()
        .expect("the retained receipt must hold at least one row")
        .expect("the committed row must parse");

    // POSITIVE CONTROL, FIRST. A refusal test that refuses everything proves nothing, and
    // this is the direction that actually breaks: a floor set one too high reddens the real
    // receipt while every mutant below still dies, which reads as a clean campaign.
    real.validate(&pin).unwrap_or_else(|reason| {
        panic!("the committed receipt must satisfy its own guard, but: {reason}")
    });

    let below = |value: u64| value.saturating_sub(1);
    let mutants: Vec<(&str, CorpusMatrixReceipt, &str)> = vec![
        (
            "compared nothing at all — the row measured to pass before this repair",
            CorpusMatrixReceipt {
                modules: 0,
                decoded: 0,
                units_compared: 0,
                corpus_digests: Vec::new(),
                per_width_ms: Vec::new(),
                wall_ms: 0,
                corpus_fixture_hash: String::new(),
                lane_source_digest_at_run: String::new(),
                ..real.clone()
            },
            "corpus digest(s)",
        ),
        (
            "one digest for three widths",
            CorpusMatrixReceipt {
                corpus_digests: real.corpus_digests[..1].to_vec(),
                ..real.clone()
            },
            "corpus digest(s)",
        ),
        (
            "one timing for three widths",
            CorpusMatrixReceipt {
                per_width_ms: real.per_width_ms[..1].to_vec(),
                ..real.clone()
            },
            "per-width timing(s)",
        ),
        (
            "a module left out of the matrix",
            CorpusMatrixReceipt {
                unmatrixed_modules: 1,
                ..real.clone()
            },
            "unmatrixed module(s)",
        ),
        (
            "one module short of the pinned corpus",
            CorpusMatrixReceipt {
                modules: below(PINNED_PRESENT_OLEAN_FLOOR),
                ..real.clone()
            },
            "present-module floor",
        ),
        (
            "one declaration short of the pinned corpus",
            CorpusMatrixReceipt {
                decoded: below(RETAINED_MATRIX_V1_DECODED_DECL_FLOOR),
                ..real.clone()
            },
            "decoded declaration(s) in matrixed modules",
        ),
        (
            "a full corpus with no unit compared",
            CorpusMatrixReceipt {
                units_compared: 0,
                ..real.clone()
            },
            "zero units compared",
        ),
        (
            "more units compared than declarations to compare",
            CorpusMatrixReceipt {
                units_compared: real.decoded + 1,
                ..real.clone()
            },
            "units compared but only",
        ),
        (
            "the whole corpus at three widths in under a millisecond",
            CorpusMatrixReceipt {
                wall_ms: 0,
                ..real.clone()
            },
            "wall_ms: 0",
        ),
        (
            "no corpus revision named",
            CorpusMatrixReceipt {
                corpus_fixture_hash: String::new(),
                ..real.clone()
            },
            "empty corpus_fixture_hash",
        ),
        (
            "no producing source named",
            CorpusMatrixReceipt {
                lane_source_digest_at_run: String::new(),
                ..real.clone()
            },
            "empty lane_source_digest_at_run",
        ),
        // The checks that existed before this repair. They are planted too, so a future
        // rewrite of `validate` cannot quietly drop one while the new mutants keep dying.
        (
            "a refutation filed as a receipt",
            CorpusMatrixReceipt {
                diverging_modules: 1,
                ..real.clone()
            },
            "diverging module(s)",
        ),
        (
            "an observation of another Reference",
            CorpusMatrixReceipt {
                pin: format!("{pin}-not"),
                ..real.clone()
            },
            "row records pin",
        ),
        (
            "widths the lane does not run",
            CorpusMatrixReceipt {
                widths: vec![1, 8],
                ..real.clone()
            },
            "row records widths",
        ),
        (
            "a class this lane cannot earn",
            CorpusMatrixReceipt {
                class: "invariant".to_string(),
                ..real.clone()
            },
            "which this lane cannot earn",
        ),
    ];

    for (mutation, receipt, expected) in mutants {
        // The reason is asserted, not merely the refusal. A rig that scored any `Err` as a
        // kill would keep reporting a clean campaign after `validate` stopped checking the
        // thing each mutant was planted against, and would credit the kill to a check that
        // had been replaced by an unrelated one (the lesson `uagk` paid for).
        let reason = receipt.validate(&pin).err().unwrap_or_else(|| {
            panic!(
                "SURVIVING MUTANT `{mutation}`: the guard accepted this row, so the retained \
                 evidence for the PG-5 waiver does not have to describe a run that happened"
            )
        });
        assert!(
            reason.contains(expected),
            "mutant `{mutation}` was refused for the wrong reason. Expected a message naming \
             `{expected}`, got: {reason}"
        );
    }
}

/// Planted divergences for `first_divergence_across_widths` (R3 of bead
/// `fln-corpus-thread-matrix-93te`).
///
/// These run in milliseconds because the comparator is a pure function over recorded
/// runs. That matters: the corpus matrix itself is expensive and will land on a cadence,
/// so the part that decides whether a divergence is *detected and named* must be provable
/// without paying for the run that produces the data.
#[test]
fn the_width_comparator_names_the_pair_and_the_unit_that_diverged() {
    fn unit(lead: &str, outcome: &str) -> UnitOutcome {
        UnitOutcome {
            lead: lead.to_string(),
            kind: "def",
            members: 1,
            outcome: outcome.to_string(),
            message: String::new(),
            steps_used: 1,
            max_depth: 1,
        }
    }
    fn run(threads: usize, digest: &str, outcomes: Vec<UnitOutcome>) -> MatrixRun {
        MatrixRun {
            threads,
            outcomes,
            stream_digest: digest.to_string(),
            accepted: 1,
            inconclusive: 0,
            rejected: BTreeMap::new(),
            steps_total: 10,
            depth_max: 3,
            duration_us: 0,
        }
    }
    let base = vec![unit("A", "accepted"), unit("B", "accepted")];

    // Negative control: without this the cases below could pass for the wrong reason.
    let clean = vec![
        run(1, "d", base.clone()),
        run(8, "d", base.clone()),
        run(32, "d", base.clone()),
    ];
    assert_eq!(first_divergence_across_widths(&clean), None);

    // A unit-level divergence must name BOTH widths, the index, and the lead.
    let mut drifted = base.clone();
    drifted[1] = unit("B", "rejected");
    let diverged = vec![
        run(1, "d", base.clone()),
        run(8, "other", drifted),
        run(32, "d", base.clone()),
    ];
    let report = first_divergence_across_widths(&diverged).expect("divergence must be found");
    assert!(
        report.contains("threads=1 vs threads=8")
            && report.contains("unit=1")
            && report.contains("lead=B"),
        "the report must name the pair and the site, not merely that something differed: {report}"
    );

    // A dropped unit must be named as a count difference. `zip` truncates, so the naive
    // comparison reported "equal prefixes" here and hid the cause.
    let truncated = vec![
        run(1, "d", base.clone()),
        run(8, "other", vec![unit("A", "accepted")]),
    ];
    let report = first_divergence_across_widths(&truncated).expect("divergence must be found");
    assert!(
        report.contains("unit count differs") && report.contains("2 vs 1"),
        "a dropped unit must be reported as a count difference: {report}"
    );

    // Identical streams with differing consumption are still a divergence: FL-INV-01
    // covers exact consumption, not just verdicts.
    let mut greedy = run(8, "d", base.clone());
    greedy.steps_total = 11;
    let consumption = vec![run(1, "d", base.clone()), greedy];
    let report = first_divergence_across_widths(&consumption).expect("divergence must be found");
    assert!(
        report.contains("consumption differs") && report.contains("steps 10 vs 11"),
        "differing consumption at equal verdicts must still diverge: {report}"
    );
}

// ---------------------------------------------------------------------------
// G0-2 acceptance (a): the chosen module set — a Std module and a defeq-heavy
// mathlib file — replayed through the one authority with verdicts diffed
// against the ReferenceKernelOracle (bead franken_lean-z6c).
//
// The legs reuse the corpus machinery but cost their import CLOSURE, never
// the whole corpus: a BFS inventory from the chosen module over the
// provisioned roots (toolchain lib, the mathlib cache's own tree, and every
// dependency package the pinned lakefile declares), then exactly one
// replayed module per leg.
// ---------------------------------------------------------------------------

/// first module-name component -> the lib dir holding that prefix's oleans.
/// The mathlib corpus location is overridable because it is host provisioning,
/// never a repository input: `FLN_MATHLIB_CORPUS`, defaulting to the path the
/// G0-1 session provisioned.
fn chosen_set_roots(reference_lib: &Path) -> Vec<(String, PathBuf)> {
    let corpus = std::env::var("FLN_MATHLIB_CORPUS")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from("/data/tmp/mathlib4-corpus"));
    let pkg = |name: &str| corpus.join(format!(".lake/packages/{name}/.lake/build/lib/lean"));
    vec![
        ("Init".to_string(), reference_lib.to_path_buf()),
        ("Std".to_string(), reference_lib.to_path_buf()),
        ("Lean".to_string(), reference_lib.to_path_buf()),
        ("Lake".to_string(), reference_lib.to_path_buf()),
        ("Batteries".to_string(), pkg("batteries")),
        ("Aesop".to_string(), pkg("aesop")),
        ("Qq".to_string(), pkg("Qq")),
        ("ProofWidgets".to_string(), pkg("proofwidgets")),
        ("ImportGraph".to_string(), pkg("importGraph")),
        ("Plausible".to_string(), pkg("plausible")),
        ("LeanSearchClient".to_string(), pkg("LeanSearchClient")),
        // Cli has no built oleans in the cache and no Mathlib module imports
        // it (it backs the cache tool itself), so it has no root here.
        ("Mathlib".to_string(), corpus.join(".lake/build/lib/lean")),
    ]
}

#[test]
fn chosen_set_routes_every_reference_top_level() {
    let reference_lib = PathBuf::from("/pinned-reference/lib/lean");
    let roots = chosen_set_roots(&reference_lib);

    for prefix in ["Init", "Std", "Lean", "Lake"] {
        assert_eq!(
            roots
                .iter()
                .find_map(|(candidate, root)| (candidate == prefix).then_some(root)),
            Some(&reference_lib),
            "the selected-module harness must route {prefix} through the pinned Reference library"
        );
    }
}

fn chosen_module_file(roots: &[(String, PathBuf)], name: &str) -> Option<PathBuf> {
    let first = name.split('.').next()?;
    let (_, root) = roots.iter().find(|(prefix, _)| prefix == first)?;
    let candidate = root.join(format!("{}.olean", name.replace('.', "/")));
    candidate.is_file().then_some(candidate)
}

fn canonical_closure_seed_queue(seeds: &[String]) -> Vec<String> {
    seeds
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .rev()
        .collect()
}

#[test]
fn multi_root_closure_preserves_every_distinct_seed() {
    let seeds = vec![
        "Mathlib.Zeta".to_string(),
        "Mathlib.Alpha".to_string(),
        "Mathlib.Zeta".to_string(),
        "Mathlib.Middle".to_string(),
    ];
    let mut queue = canonical_closure_seed_queue(&seeds);
    let mut popped = Vec::new();
    while let Some(seed) = queue.pop() {
        popped.push(seed);
    }
    assert_eq!(
        popped,
        ["Mathlib.Alpha", "Mathlib.Middle", "Mathlib.Zeta"],
        "a multi-root closure must neither drop a distinct seed nor replay duplicates"
    );
}

/// BFS inventory from one or more chosen modules through decoded import rows, folded
/// with the same scheme as `inventory_present_oleans` so the two fixture
/// hashes mean the same thing over their different populations.
fn closure_inventory_from_seeds(
    roots: &[(String, PathBuf)],
    seeds: &[String],
) -> Result<CorpusInventory, String> {
    if seeds.is_empty() {
        return Err("closure inventory needs at least one seed module".to_string());
    }
    let mut modules = BTreeMap::new();
    let mut decoded = 0_u64;
    let mut oracle_skipped = 0_u64;
    let mut aggregate = Vec::new();
    aggregate.extend_from_slice(b"fln.kernel-reference-corpus.inventory/1\0");
    let mut queue = canonical_closure_seed_queue(seeds);
    while let Some(name) = queue.pop() {
        if modules.contains_key(&name) {
            continue;
        }
        let path = chosen_module_file(roots, &name)
            .ok_or_else(|| format!("no provisioned olean for import {name}"))?;
        let decoded_module = decode_corpus_module(&path, &name)?;
        let infos = decoded_module.infos;
        let decoded_here = u64::try_from(infos.len())
            .map_err(|_| format!("declaration count overflow in {}", path.display()))?;
        let skipped_here = infos
            .iter()
            .filter(|info| reference_replay_skips(info))
            .count() as u64;
        let olean_hash = decoded_module.olean_hash;
        let imports = decoded_module.imports;
        for import in &imports {
            if !modules.contains_key(import) {
                queue.push(import.clone());
            }
        }
        modules.insert(
            name.clone(),
            CorpusModule {
                name: name.clone(),
                path,
                olean_hash: olean_hash.clone(),
                imports,
                decoded: decoded_here,
                oracle_skipped: skipped_here,
            },
        );
        decoded = decoded
            .checked_add(decoded_here)
            .ok_or_else(|| "decoded declaration census overflow".to_string())?;
        oracle_skipped = oracle_skipped
            .checked_add(skipped_here)
            .ok_or_else(|| "oracle-skipped declaration census overflow".to_string())?;
        aggregate.extend_from_slice(&(name.len() as u64).to_le_bytes());
        aggregate.extend_from_slice(name.as_bytes());
        aggregate.extend_from_slice(&(olean_hash.len() as u64).to_le_bytes());
        aggregate.extend_from_slice(olean_hash.as_bytes());
    }
    let present = modules.keys().cloned().collect::<BTreeSet<_>>();
    let mut missing_imports = Vec::new();
    for module in modules.values() {
        for import in module.imports.difference(&present) {
            missing_imports.push((module.name.clone(), import.clone()));
        }
    }
    Ok(CorpusInventory {
        modules,
        decoded,
        oracle_skipped,
        missing_imports,
        fixture_hash: hash(Domain::Fixture, &aggregate).to_hex(),
    })
}

fn closure_inventory(roots: &[(String, PathBuf)], chosen: &str) -> Result<CorpusInventory, String> {
    closure_inventory_from_seeds(roots, &[chosen.to_string()])
}

/// One chosen-set leg: the verdict census of one replayed module over its
/// faithfully reconstructed import context, plus the context's own facts.
// The two `expect`ed fields are MistyEagle's mid-flight work, swept into a commit
// anonymously at bc4e1b3d before their readers landed. `expect` (not `allow`) is the
// honest deferral: it passes only while the fields are unread, and reddens the moment
// the readers land, forcing removal of the attribute — a typed TODO, not a suppression.
#[expect(
    dead_code,
    reason = "fields await their readers in the remainder of this in-flight change"
)]
struct ChosenLegReport {
    module: String,
    closure_modules: u64,
    closure_decoded: u64,
    context_faithful: bool,
    collision_count: u64,
    units: u64,
    decls_total: u64,
    unchecked: BTreeMap<String, u64>,
    artifact_incomplete: u64,
    accepted: u64,
    rejected: BTreeMap<String, u64>,
    inconclusive: u64,
    stream_digest: String,
    wall_ms: u64,
}

struct PreparedChosenModule {
    prep: PreparedReplay,
    collision_count: u64,
}

fn prepare_chosen_module(
    inventory: &CorpusInventory,
    chosen: &str,
) -> Result<PreparedChosenModule, String> {
    let order = corpus_module_order(inventory)?;
    let order_index = order
        .iter()
        .enumerate()
        .map(|(index, name)| (name.clone(), index))
        .collect::<HashMap<_, _>>();
    let mut states = BTreeMap::<String, CorpusFixtureState>::new();
    for module_name in &order {
        let module = &inventory.modules[module_name];
        let decoded_module = decode_corpus_module(&module.path, &module.name)?;
        let current_hash = decoded_module.olean_hash;
        let infos = decoded_module.infos;
        if current_hash != module.olean_hash {
            return Err(format!(
                "{} changed between inventory and replay",
                module.name
            ));
        }
        let (active_infos, _, _) = reference_active_rows(&infos);
        let ReconstructedImportContext {
            imported: imported_context,
            closure,
            faithful: context_faithful,
            collisions,
        } = reconstruct_import_context(module, inventory, &order_index, &states);
        if module_name == chosen {
            if !context_faithful {
                return Err(format!(
                    "{chosen}: import context not faithfully representable ({} collisions)",
                    collisions.len()
                ));
            }
            let prep = prepare_replay_from(
                imported_context.environment.clone(),
                Some(&imported_context),
                &active_infos,
                false,
            );
            return Ok(PreparedChosenModule {
                prep,
                collision_count: collisions.len() as u64,
            });
        }
        let (context, _) =
            extend_reference_fixture_environment(imported_context, &active_infos, &module.name)?;
        states.insert(
            module.name.clone(),
            CorpusFixtureState {
                closure,
                context,
                active_infos,
                faithful: context_faithful,
            },
        );
    }
    Err(format!(
        "chosen module {chosen} absent from its own closure"
    ))
}

fn run_chosen_leg(inventory: &CorpusInventory, chosen: &str) -> Result<ChosenLegReport, String> {
    let started = Instant::now();
    let PreparedChosenModule {
        prep,
        collision_count,
    } = prepare_chosen_module(inventory, chosen)?;
    let run = check_matrix_run(&prep, 1, Budget::DEFAULT);
    Ok(ChosenLegReport {
        module: chosen.to_string(),
        closure_modules: inventory.modules.len() as u64,
        closure_decoded: inventory.decoded,
        context_faithful: true,
        collision_count,
        units: prep.items.len() as u64,
        decls_total: prep.decls_total as u64,
        unchecked: prep
            .unchecked
            .iter()
            .map(|(kind, count)| (kind.to_string(), *count))
            .collect(),
        artifact_incomplete: prep.artifact_incomplete.len() as u64,
        accepted: run.accepted,
        rejected: run.rejected,
        inconclusive: run.inconclusive,
        stream_digest: run.stream_digest,
        wall_ms: started.elapsed().as_millis() as u64,
    })
}

/// Select exactly one declaration from a provisioned Reference module and
/// report its governed kernel consumption.
///
/// This is intentionally an ignored, operator-selected diagnostic rather than
/// a per-commit claim. It reuses the chosen-set closure reconstruction, checks
/// the selected admission unit on an explicit stack, and refuses missing or
/// non-unique selectors. Run with:
///
///   FLN_CORPUS_PROBE_MODULE=Init.Data.Nat.Bitwise.Basic \
///   FLN_CORPUS_PROBE_DECL=Nat.shiftRight_eq_div_pow._f \
///   cargo test -p fln-conformance --test kernel_replay \
///     selected_real_module_resource_probe -- --ignored --nocapture
///
/// Set `FLN_CORPUS_PROBE_DIAGNOSTIC=1` to print the bounded authoritative
/// diagnostic in addition to its digest when investigating a rejection.
/// `FLN_CORPUS_PROBE_ENV` may additionally name a comma-separated set of
/// constants whose decoded kinds and definition bodies should be shown.
/// `FLN_CORPUS_PROBE_EXPECT` makes the process fail unless the exact rendered
/// outcome matches (for example, `accepted` or `rejected:TypeMismatch`).
///
/// Omitting `FLN_CORPUS_PROBE_STACK_BYTES` and `FLN_CORPUS_PROBE_STEPS` uses
/// `Budget::DEFAULT` on its required stack. Supplying either value is a
/// diagnostic-only way to derive an explicitly calibrated budget for that
/// stack; the output always records both values, so it cannot be mistaken for
/// the default-budget observation.
#[ignore = "cost: decodes one selected module's real import closure; on-demand resource probe"]
#[test]
fn selected_real_module_resource_probe() {
    let chosen = std::env::var("FLN_CORPUS_PROBE_MODULE")
        .expect("FLN_CORPUS_PROBE_MODULE must name one provisioned Reference module");
    let selector = std::env::var("FLN_CORPUS_PROBE_DECL")
        .expect("FLN_CORPUS_PROBE_DECL must name exactly one declaration");
    assert!(
        !chosen.trim().is_empty() && !selector.trim().is_empty(),
        "resource-probe module and declaration selectors must be non-empty"
    );
    let stack_override = match std::env::var("FLN_CORPUS_PROBE_STACK_BYTES") {
        Ok(raw) => {
            let stack_bytes = raw
                .parse::<usize>()
                .expect("FLN_CORPUS_PROBE_STACK_BYTES must be a base-10 byte count");
            assert!(
                stack_bytes >= 64 * 1024,
                "resource-probe stack must be at least 64 KiB"
            );
            Some(stack_bytes)
        }
        Err(std::env::VarError::NotPresent) => None,
        Err(error) => panic!("read FLN_CORPUS_PROBE_STACK_BYTES: {error}"),
    };
    let steps_override = match std::env::var("FLN_CORPUS_PROBE_STEPS") {
        Ok(raw) => Some(
            raw.parse::<u64>()
                .expect("FLN_CORPUS_PROBE_STEPS must be a base-10 step count"),
        ),
        Err(std::env::VarError::NotPresent) => None,
        Err(error) => panic!("read FLN_CORPUS_PROBE_STEPS: {error}"),
    };
    let stack_bytes = stack_override.unwrap_or(KERNEL_REPLAY_WORKER_STACK_BYTES);
    let steps = steps_override.unwrap_or(Budget::DEFAULT_STEPS);
    assert!(steps > 0, "resource-probe step budget must be nonzero");
    let budget = if stack_override.is_none() && steps_override.is_none() {
        Budget::DEFAULT
    } else {
        Budget::derive(
            StackMeasurement::k1_here(),
            ExecConfig::current(),
            stack_bytes,
            steps,
        )
    };

    let reference_lib = reference_lib().expect("pinned toolchain required for the resource probe");
    let roots = chosen_set_roots(&reference_lib);
    let inventory = closure_inventory(&roots, &chosen)
        .unwrap_or_else(|error| panic!("{chosen}: closure inventory failed: {error}"));
    assert!(
        inventory.missing_imports.is_empty(),
        "{chosen}: closure has unresolved imports: {:?}",
        inventory.missing_imports
    );
    let PreparedChosenModule {
        prep,
        collision_count,
    } = prepare_chosen_module(&inventory, &chosen)
        .unwrap_or_else(|error| panic!("{chosen}: replay preparation failed: {error}"));

    let matches = prep
        .items
        .iter()
        .enumerate()
        .filter(|(_, item)| {
            item.member_names
                .iter()
                .any(|name| name.to_display_string() == selector)
        })
        .collect::<Vec<_>>();
    assert!(
        matches.len() == 1,
        "{chosen}: declaration selector `{selector}` matched {} admission units; expected exactly one",
        matches.len()
    );
    let (unit_index, item) = matches[0];
    let verdict = check_work_item_with_stack(item, budget, stack_bytes);
    let outcome = unit_outcome(item, &verdict);
    if let Ok(expected) = std::env::var("FLN_CORPUS_PROBE_EXPECT") {
        assert!(
            !expected.is_empty(),
            "FLN_CORPUS_PROBE_EXPECT must be a non-empty exact outcome"
        );
        assert!(
            outcome.outcome == expected,
            "{chosen}: declaration `{selector}` produced `{}`; expected `{expected}`",
            outcome.outcome
        );
    }
    let message_digest = if outcome.message.is_empty() {
        "none".to_string()
    } else {
        hash(Domain::Fixture, outcome.message.as_bytes()).to_hex()
    };
    if std::env::var_os("FLN_CORPUS_PROBE_DIAGNOSTIC").is_some() {
        eprintln!("kernel_resource_probe diagnostic={}", outcome.message);
        eprintln!(
            "kernel_resource_probe selected_type={}",
            shape(&item.info.constant_val().type_, 10)
        );
        match &item.info {
            ConstantInfo::Defn(value) => eprintln!(
                "kernel_resource_probe selected_value=definition safety={:?} hints={:?} {}",
                value.safety,
                value.hints,
                shape(&value.value, 12)
            ),
            ConstantInfo::Thm(value) => eprintln!(
                "kernel_resource_probe selected_value=theorem {}",
                shape(&value.value, 12)
            ),
            ConstantInfo::Opaque(value) => eprintln!(
                "kernel_resource_probe selected_value=opaque {}",
                shape(&value.value, 12)
            ),
            _ => {}
        }
    }
    if let Ok(names) = std::env::var("FLN_CORPUS_PROBE_ENV") {
        for entry in names.split(',') {
            let mut target = Name::anonymous();
            for segment in entry.trim().split('.') {
                target = Name::str(target, segment);
            }
            match item.env.find(&target) {
                Some(ConstantInfo::Defn(definition)) => eprintln!(
                    "kernel_resource_probe env {}=definition safety={:?} hints={:?} value={}",
                    entry.trim(),
                    definition.safety,
                    definition.hints,
                    shape(&definition.value, 10)
                ),
                Some(other) => eprintln!(
                    "kernel_resource_probe env {}={}",
                    entry.trim(),
                    other.kind_name()
                ),
                None => eprintln!("kernel_resource_probe env {}=ABSENT", entry.trim()),
            }
        }
    }
    eprintln!(
        "kernel_resource_probe module={} declaration={} unit_index={} unit_lead={} \
         kind={} members={} outcome={} steps_used={} max_depth={} \
         budget_steps={} budget_depth={} stack_bytes={} closure_modules={} \
         closure_decoded={} collision_count={} diagnostic_digest={}",
        chosen,
        selector,
        unit_index,
        outcome.lead,
        outcome.kind,
        outcome.members,
        outcome.outcome,
        outcome.steps_used,
        outcome.max_depth,
        budget.steps,
        budget.depth,
        stack_bytes,
        inventory.modules.len(),
        inventory.decoded,
        collision_count,
        message_digest,
    );
    assert!(
        !matches!(verdict, Outcome::InternalFault(_)),
        "{chosen}:{selector}: an internal fault is never a resource observation"
    );
}

fn validate_leanchecker_authority_contract(script: &str, findings: &str) -> Result<(), String> {
    for required in [
        "ReferenceKernelOracle",
        r#"\"authority\":\"ReferenceKernelOracle\""#,
        "reference-kernel-oracle-agreement",
        "not_applicable_reference_kernel_oracle",
    ] {
        if !script.contains(required) {
            return Err(format!(
                "leanchecker lane lacks required authority token {required:?}"
            ));
        }
    }
    for forbidden in [
        "FOREIGN kernel witness",
        "independent binary",
        "independent kernel-replay tool",
        "kernel-witness-agreement",
        "not_applicable_foreign_kernel_witness",
        "foreign-witness differential green",
    ] {
        if script.contains(forbidden) {
            return Err(format!(
                "leanchecker lane revives independent-witness claim {forbidden:?}"
            ));
        }
    }

    let normalized_findings = findings.split_whitespace().collect::<Vec<_>>().join(" ");
    for required in [
        "The Reference-kernel oracle differential",
        "ReferenceKernelOracle",
        "a second execution, not a second independent opinion",
        "does **not** satisfy the independent-witness leg",
    ] {
        if !normalized_findings.contains(required) {
            return Err(format!(
                "kernel replay findings lack required authority statement {required:?}"
            ));
        }
    }
    for forbidden in [
        "The foreign-witness differential",
        "Reference's own independent",
        "independent binary re-confirms",
        "independent foreign kernel",
    ] {
        if normalized_findings.contains(forbidden) {
            return Err(format!(
                "kernel replay findings revive independent-witness claim {forbidden:?}"
            ));
        }
    }
    Ok(())
}

/// `leanchecker` executes the pinned Reference kernel. A process boundary must
/// never be promoted into an implementation-independence claim.
#[test]
fn leanchecker_lane_is_bound_to_reference_kernel_oracle_authority() {
    let root = fln_conformance::checked_manifest_dir!().join("../..");
    let script = std::fs::read_to_string(root.join("scripts/tribunal/leanchecker_witness.sh"))
        .expect("read leanchecker lane");
    let findings =
        std::fs::read_to_string(root.join("tribunal/fixtures/c3/KERNEL_REPLAY_FINDINGS.md"))
            .expect("read kernel replay findings");

    validate_leanchecker_authority_contract(&script, &findings)
        .expect("live lane and findings must preserve ReferenceKernelOracle authority");

    let authority_mutant = script.replace("ReferenceKernelOracle", "ForeignIndependent");
    assert!(
        validate_leanchecker_authority_contract(&authority_mutant, &findings).is_err(),
        "an authority mutant must not retain independent corroboration"
    );

    let prose_mutant = findings.replacen(
        "a second execution, not a second independent opinion",
        "an independent opinion",
        1,
    );
    assert!(
        validate_leanchecker_authority_contract(&script, &prose_mutant).is_err(),
        "a findings mutant must not upgrade re-execution into independence"
    );
}

/// The two acceptance-(a) legs beyond Init: a Std module and one defeq-heavy
/// mathlib file, each replayed through the one authority and diffed against
/// the pinned leanchecker as the ReferenceKernelOracle witness (the review
/// amendment's authority classification: leanchecker embeds the Reference C++
/// kernel, so it is ReferenceKernelOracle, never ForeignIndependent).
///
/// `#[ignore]`d: the mathlib leg costs its ~200-module closure decode plus a
/// defeq-heavy replay. By default the on-demand lane verifies the committed
/// receipt's semantic rows without rewriting it. Set
/// `FLN_UPDATE_CHOSEN_SET_RECEIPT=1` to atomically regenerate the pin-keyed
/// receipt after reviewing an intentional semantic change. Run with:
///   cargo test -p fln-conformance --test kernel_replay \
///     chosen_set_replays_and_witnesses -- --ignored --nocapture
#[ignore = "cost: two closure inventories plus a defeq-heavy replay; on-demand probe lane, receipt verified by default"]
#[test]
fn chosen_set_replays_and_witnesses() {
    let reference_lib = reference_lib().expect("pinned toolchain required for the chosen set");
    let roots = chosen_set_roots(&reference_lib);
    for (_, root) in &roots {
        // A root that does not exist makes the leg's provenance a lie by
        // omission; refuse loudly rather than silently narrowing the closure.
        assert!(root.is_dir(), "chosen-set root missing: {}", root.display());
    }
    // Std.Data.HashMap.Basic: real data-structure code (structure projections,
    // instances, Nat-accelerated index arithmetic) rather than the Std.Do
    // aggregator, which decodes to zero replay units and so proves nothing.
    let legs = ["Std.Data.HashMap.Basic", "Mathlib.Order.Basic"];
    let mut reports = Vec::new();
    for leg in legs {
        let inventory = closure_inventory(&roots, leg)
            .unwrap_or_else(|error| panic!("{leg}: closure inventory failed: {error}"));
        assert!(
            inventory.missing_imports.is_empty(),
            "{leg}: closure has unresolved imports: {:?}",
            inventory.missing_imports
        );
        let report = run_chosen_leg(&inventory, leg)
            .unwrap_or_else(|error| panic!("{leg}: replay failed: {error}"));
        eprintln!(
            "chosen_set leg={} closure_modules={} closure_decoded={} units={} \
             accepted={} rejected={:?} inconclusive={} artifact_incomplete={} \
             unchecked={:?} digest={} wall_ms={}",
            report.module,
            report.closure_modules,
            report.closure_decoded,
            report.units,
            report.accepted,
            report.rejected,
            report.inconclusive,
            report.artifact_incomplete,
            report.unchecked,
            report.stream_digest,
            report.wall_ms,
        );
        reports.push(report);
    }
    // The ReferenceKernelOracle differential: the pinned leanchecker replays
    // each chosen module through the Reference C++ kernel over the same
    // provisioned oleans (LEAN_PATH = every chosen-set root), and its verdict
    // MUST be acceptance — the Reference accepted these modules when it wrote
    // them. This is a second execution of that implementation, not an
    // independent witness.
    let search_roots = roots
        .iter()
        .map(|(_, root)| root.as_path())
        .collect::<Vec<_>>();
    let mut witness_rows = Vec::new();
    for report in &reports {
        let verdict = run_leanchecker_with_search_roots(
            &reference_lib,
            &search_roots,
            std::slice::from_ref(&report.module),
            DEFAULT_LEANCHECKER_TIMEOUT,
        )
        .unwrap_or_else(|error| panic!("{}: sealed leanchecker failed: {error}", report.module));
        let accepted = matches!(verdict, ReferenceCorpusVerdict::Accepted { .. });
        eprintln!(
            "chosen_set witness module={} verdict={} detail={:?}",
            report.module,
            if accepted { "accepted" } else { "not_accepted" },
            verdict,
        );
        assert!(
            accepted,
            "Reference kernel oracle did not accept {}",
            report.module
        );
        witness_rows.push((report.module.clone(), accepted));
    }
    // The committed receipt: per-leg census plus witness agreement, keyed by
    // the pin so advancing SUITE.lock makes the file absent rather than stale.
    let evidence_dir = fln_conformance::checked_manifest_dir!()
        .join("../../crates/fln-conformance/evidence/g02_kernel_verdict");
    let receipt_path = evidence_dir.join("chosen_set_v4.32.0.jsonl");
    let mut receipt = String::new();
    for (report, (_, witness_accepted)) in reports.iter().zip(&witness_rows) {
        let rejected_json = if report.rejected.is_empty() {
            "{}".to_string()
        } else {
            format!(
                "{{{}}}",
                report
                    .rejected
                    .iter()
                    .map(|(class, count)| format!("\"{class}\":{count}"))
                    .collect::<Vec<_>>()
                    .join(",")
            )
        };
        receipt.push_str(&format!(
            "{{\"schema\":\"fln-g02-chosen-set/1\",\"module\":{m},\"closure_modules\":{cm},\"closure_decoded\":{cd},\"units\":{u},\"decls_total\":{dt},\"accepted\":{a},\"rejected\":{r},\"inconclusive\":{i},\"artifact_incomplete\":{ai},\"witness\":\"ReferenceKernelOracle:leanchecker\",\"witness_accepted\":{w},\"stream_digest\":{sd},\"wall_ms\":{wm}}}\n",
            m = json_string(&report.module),
            cm = report.closure_modules,
            cd = report.closure_decoded,
            u = report.units,
            dt = report.decls_total,
            a = report.accepted,
            r = rejected_json,
            i = report.inconclusive,
            ai = report.artifact_incomplete,
            w = witness_accepted,
            sd = json_string(&report.stream_digest),
            wm = report.wall_ms,
        ));
    }
    let mode = chosen_set_receipt_mode(std::env::var_os(CHOSEN_SET_RECEIPT_UPDATE_ENV).as_deref())
        .unwrap_or_else(|error| panic!("chosen-set receipt mode refused: {error}"));
    match mode {
        ChosenSetReceiptMode::Verify => {
            let retained = std::fs::read_to_string(&receipt_path).unwrap_or_else(|error| {
                panic!(
                    "read retained chosen-set receipt {}: {error}; regenerate explicitly with {}=1 only after reviewing the live result",
                    receipt_path.display(),
                    CHOSEN_SET_RECEIPT_UPDATE_ENV,
                )
            });
            verify_chosen_set_receipt(&receipt, &retained).unwrap_or_else(|error| {
                panic!(
                    "retained chosen-set receipt {} is stale: {error}; regenerate explicitly with {}=1 only after reviewing the live result",
                    receipt_path.display(),
                    CHOSEN_SET_RECEIPT_UPDATE_ENV,
                )
            });
            eprintln!(
                "chosen_set receipt verified: {} ({} legs; wall_ms retained as run telemetry)",
                receipt_path.display(),
                reports.len()
            );
        }
        ChosenSetReceiptMode::Regenerate => {
            std::fs::create_dir_all(&evidence_dir).expect("create g02 evidence dir");
            fln::publish_file_atomic(receipt.as_bytes(), &receipt_path)
                .expect("atomically regenerate chosen-set receipt");
            eprintln!(
                "chosen_set receipt regenerated: {} ({} legs)",
                receipt_path.display(),
                reports.len()
            );
        }
    }
}

const CHOSEN_SET_RECEIPT_UPDATE_ENV: &str = "FLN_UPDATE_CHOSEN_SET_RECEIPT";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ChosenSetReceiptMode {
    Verify,
    Regenerate,
}

fn chosen_set_receipt_mode(
    value: Option<&std::ffi::OsStr>,
) -> Result<ChosenSetReceiptMode, String> {
    match value {
        None => Ok(ChosenSetReceiptMode::Verify),
        Some(value) if value == "1" => Ok(ChosenSetReceiptMode::Regenerate),
        Some(value) => Err(format!(
            "{CHOSEN_SET_RECEIPT_UPDATE_ENV} must be absent for verification or exactly 1 for regeneration, got {value:?}"
        )),
    }
}

fn chosen_set_receipt_semantics(receipt: &str) -> Result<String, String> {
    if !receipt.ends_with('\n') {
        return Err("receipt must end with a newline".to_string());
    }
    let mut semantic = String::new();
    for (index, line) in receipt.lines().enumerate() {
        if line.is_empty() {
            return Err(format!("receipt row {} is empty", index + 1));
        }
        let (prefix, wall_ms) = line
            .rsplit_once(",\"wall_ms\":")
            .ok_or_else(|| format!("receipt row {} has no terminal wall_ms", index + 1))?;
        let wall_ms = wall_ms
            .strip_suffix('}')
            .ok_or_else(|| format!("receipt row {} has a malformed wall_ms tail", index + 1))?;
        wall_ms.parse::<u128>().map_err(|error| {
            format!(
                "receipt row {} has a non-numeric wall_ms {wall_ms:?}: {error}",
                index + 1
            )
        })?;
        semantic.push_str(prefix);
        semantic.push_str("}\n");
    }
    Ok(semantic)
}

fn verify_chosen_set_receipt(expected: &str, retained: &str) -> Result<(), String> {
    let expected = chosen_set_receipt_semantics(expected)?;
    let retained = chosen_set_receipt_semantics(retained)?;
    if expected == retained {
        return Ok(());
    }
    Err(format!(
        "semantic rows differ\n--- retained semantics\n{retained}--- live semantics\n{expected}"
    ))
}

#[test]
fn chosen_set_receipt_mode_requires_an_exact_regeneration_opt_in() {
    assert_eq!(
        chosen_set_receipt_mode(None),
        Ok(ChosenSetReceiptMode::Verify)
    );
    assert_eq!(
        chosen_set_receipt_mode(Some(std::ffi::OsStr::new("1"))),
        Ok(ChosenSetReceiptMode::Regenerate)
    );
    for refused in ["", "0", "true", "yes", "2"] {
        assert!(
            chosen_set_receipt_mode(Some(std::ffi::OsStr::new(refused))).is_err(),
            "a non-canonical opt-in must not enable receipt replacement: {refused:?}"
        );
    }
}

#[test]
fn chosen_set_receipt_verification_ignores_only_wall_clock_telemetry() {
    let first = concat!(
        "{\"schema\":\"fln-g02-chosen-set/1\",\"module\":\"Std.A\",\"stream_digest\":\"aaa\",\"wall_ms\":10}\n",
        "{\"schema\":\"fln-g02-chosen-set/1\",\"module\":\"Mathlib.B\",\"stream_digest\":\"bbb\",\"wall_ms\":20}\n",
    );
    let different_timing = first.replace("\"wall_ms\":10", "\"wall_ms\":999");
    verify_chosen_set_receipt(first, &different_timing)
        .expect("wall-clock telemetry is not semantic receipt identity");

    let stale_digest = first.replace("\"aaa\"", "\"stale\"");
    let missing_row = first
        .lines()
        .next()
        .map(|line| format!("{line}\n"))
        .unwrap();
    let extra_row = format!("{first}{first}");
    let swapped_rows = first.lines().rev().collect::<Vec<_>>().join("\n") + "\n";
    for (label, candidate) in [
        ("stale digest", stale_digest),
        ("missing row", missing_row),
        ("extra row", extra_row),
        ("swapped rows", swapped_rows),
    ] {
        assert!(
            verify_chosen_set_receipt(first, &candidate).is_err(),
            "verification must refuse a {label}"
        );
    }

    for malformed in [
        "{\"schema\":\"fln-g02-chosen-set/1\"}\n",
        "{\"schema\":\"fln-g02-chosen-set/1\",\"wall_ms\":-1}\n",
        "{\"schema\":\"fln-g02-chosen-set/1\",\"wall_ms\":x}\n",
        "{\"schema\":\"fln-g02-chosen-set/1\",\"wall_ms\":1}",
    ] {
        assert!(chosen_set_receipt_semantics(malformed).is_err());
    }
}
