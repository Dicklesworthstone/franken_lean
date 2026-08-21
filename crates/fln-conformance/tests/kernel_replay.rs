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
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Mutex, OnceLock};
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

/// The replay order respects every edge, scans every member, and breaks ties by
/// unit index.
///
/// **The function that decides replay order had no test.** Its doc makes three
/// claims -- a unit is admitted only after every unit owning a constant ANY of
/// its members mention, ties are broken in unit-creation order so the replay is
/// deterministic, and units in a dependency cycle come back separately -- and
/// nothing anywhere checked one of them. It runs on the corpus, so on this host
/// it had never executed at all.
///
/// **Getting it wrong is not a crash, it is a wrong diagnosis.** A unit checked
/// before the unit it depends on is submitted to a kernel whose environment does
/// not hold that constant yet. The verdict is a missing-constant rejection --
/// indistinguishable, downstream, from the artifact being incomplete. The replay
/// would report the corpus as broken and be believed.
///
/// **The fixture is synthetic and tiny, and the assertions are on the RELATION,
/// not on the order that comes out.** A golden list would pass for a function
/// that had stopped consulting the edges at all, as long as the fixture happened
/// to be numbered conveniently. The edges are declared here by construction --
/// each axiom's type either names one constant or is a sort -- so the expected
/// relation is written independently of `dependencies`, which is the function
/// under test's own machinery.
///
/// **Each assertion kills a specific way of being wrong.**
/// - `C` before `A` and before the `B, E` block: an implementation that ignored
///   edges and emitted `0..n` puts `A` first.
/// - `C` before the `B, E` block specifically: `E` is that unit's SECOND member
///   and is the only one naming `C`. An implementation scanning just the first
///   member sees no edge, the block starts ready, and being unit 1 it wins the
///   tie against unit 2 and comes out first.
/// - `A` before the block: both are released at the same instant, by `C`. This
///   is the tie, and it is the whole determinism claim -- a ready set drained in
///   hash order satisfies every other assertion here.
#[test]
fn the_replay_order_respects_every_edge_and_breaks_ties_by_unit_index() {
    use fln_env::constants::{AxiomVal, ConstantVal};

    fn axiom(name: &str, mentions: Option<&str>) -> ConstantInfo {
        // A type that names one constant, or a sort, which names none. Nothing
        // else is needed: `dependencies` reads the type of an axiom and stops.
        let type_ = match mentions {
            Some(dep) => Expr::const_(Name::str(Name::anonymous(), dep), Vec::new()),
            None => Expr::sort(Level::zero()),
        };
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: Name::str(Name::anonymous(), name),
                level_params: Vec::new(),
                type_,
            },
            is_unsafe: false,
        })
    }

    let infos = vec![
        axiom("A", Some("C")),
        axiom("B", None),
        axiom("E", Some("C")),
        axiom("C", None),
        axiom("D", Some("A")),
    ];
    // Unit 1 is a BLOCK whose first member names nothing and whose second names
    // `C`. That asymmetry is the fixture's entire point.
    let units = vec![vec![0], vec![1, 2], vec![3], vec![4]];

    let (order, cyclic) = unit_topological_order(&infos, &units);

    // TOTAL, AND EACH UNIT EXACTLY ONCE. Without this, every ordering claim
    // below is satisfiable by dropping the units that would have violated it.
    assert!(
        cyclic.is_empty(),
        "this fixture has no cycle; units {cyclic:?} were reported as cyclic"
    );
    assert_eq!(
        order.len(),
        units.len(),
        "every unit must be placed: {order:?}"
    );
    assert_eq!(
        order.iter().copied().collect::<HashSet<_>>().len(),
        units.len(),
        "a unit was placed twice: {order:?}"
    );

    let at = |unit: usize| {
        order
            .iter()
            .position(|&u| u == unit)
            .unwrap_or_else(|| panic!("unit {unit} is missing from {order:?}"))
    };

    assert!(
        at(2) < at(0),
        "`A` depends on `C`, so unit 2 must precede unit 0. If it does not, the edges are not \
         being consulted and the replay submits `A` to a kernel that has not admitted `C`: \
         {order:?}"
    );
    assert!(
        at(2) < at(1),
        "the block's SECOND member `E` names `C`, so unit 2 must precede unit 1. This is the \
         assertion that pins `any of its members`: scan only the first member and the block \
         starts ready, wins the tie against unit 2, and is replayed before its dependency: \
         {order:?}"
    );
    assert!(
        at(0) < at(3),
        "`D` depends on `A`, so unit 0 must precede unit 3: {order:?}"
    );
    assert!(
        at(0) < at(1),
        "units 0 and 1 are released at the same instant, by unit 2, so the tie must be broken by \
         unit index. A ready set drained in hash order satisfies every other assertion here and \
         makes the replay order differ between runs of the same corpus: {order:?}"
    );
}

/// A dependency cycle is reported, not silently dropped.
///
/// **The caller replays `order` and then `cyclic`.** If a cycle made units
/// vanish from both, they would never be checked and the run would report a
/// smaller corpus rather than a failure -- the empty-referent shape. So the
/// separation has to be total, and that is what is asserted: nothing placed,
/// both units returned, in unit order.
#[test]
fn units_in_a_dependency_cycle_come_back_separately_and_in_unit_order() {
    use fln_env::constants::{AxiomVal, ConstantVal};

    fn mutually_referring(name: &str, dep: &str) -> ConstantInfo {
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: Name::str(Name::anonymous(), name),
                level_params: Vec::new(),
                type_: Expr::const_(Name::str(Name::anonymous(), dep), Vec::new()),
            },
            is_unsafe: false,
        })
    }

    let infos = vec![mutually_referring("F", "G"), mutually_referring("G", "F")];
    let units = vec![vec![0], vec![1]];

    let (order, cyclic) = unit_topological_order(&infos, &units);

    assert!(
        order.is_empty(),
        "neither unit can be admitted before the other, so nothing is topologically placed: \
         {order:?}"
    );
    assert_eq!(
        cyclic,
        vec![0, 1],
        "both units must be REPORTED, in unit order. A cycle that dropped its members would \
         leave them unchecked and the run would look like a smaller corpus rather than a \
         failure"
    );
    assert_eq!(
        order.len() + cyclic.len(),
        units.len(),
        "the two results must partition the units, or some unit is replayed twice or not at all"
    );
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
    // THE PATH'S COMPONENTS ARE NOT THE NAME'S SEGMENTS, and the guard above
    // inspects the wrong one. `Component::Normal` is never empty, so
    // `part.is_empty()` cannot fire on anything the parser produces -- while the
    // JOIN can still mint an empty segment out of perfectly non-empty
    // components: `x..olean` has extension `olean` and stem `x.`, so `A/x..olean`
    // projects to `A.x.`, whose last segment has no characters. The hazard the
    // guard names is real; it was being looked for in the one place it cannot
    // appear.
    //
    // Such a name can never match an import recorded inside an olean, so the
    // module joins the census, inflates the count, resolves against nothing, and
    // reads downstream as a corpus with unresolved imports rather than as a file
    // that should not have been named.
    let name = parts.join(".");
    if name.split('.').any(str::is_empty) {
        return Err(format!(
            "{} projects to a module name with an empty segment (`{name}`); a segment with no \
             characters names nothing and can never match an import",
            path.display()
        ));
    }
    Ok(name)
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
    read_corpus_module_part_with(path, || fs::read(path))
}

/// The same reader with its READ as a parameter, so the ORDER can be observed.
///
/// **The cap's entire value is that it refuses before allocating.** Both cap
/// sites use one constant, so this one refuses nothing the aggregate would not
/// also refuse -- a version that checked after `fs::read` would return the same
/// `Err`, with the same words, for the same file, having first pulled half a
/// gigabyte into memory. Every assertion anyone can write against the RESULT
/// passes either way, which is why the ordering went unpinned when the cap
/// itself was planted.
///
/// Taking the read as an argument is what makes the difference observable
/// without observing an allocation: a caller can pass a reader that must never
/// run. Production passes `fs::read` one line above, so the two cannot drift in
/// what they read -- only in when.
fn read_corpus_module_part_with(
    path: &Path,
    read_bytes: impl FnOnce() -> std::io::Result<Vec<u8>>,
) -> Result<Vec<u8>, String> {
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
    read_bytes().map_err(|error| format!("read {}: {error}", path.display()))
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
    // REDUNDANT AND KEPT, for the same measured reason as the sort in
    // `walk_olean_inventory`: the helper's output is already in this order. It
    // stays because `modules[i]` must be the projection of `oleans[i]`, and that
    // correspondence is only true while BOTH sides order paths the same way --
    // so the two sites are a matched pair, and removing one of them alone is the
    // change that would silently break the pairing.
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
    carve_out_in(CORPUS_CARVE_OUTS, name)
}

/// The same lookup over an explicitly supplied registry.
///
/// `CORPUS_CARVE_OUTS` is EMPTY, so `corpus_carve_out` can only ever return
/// `None` and its semantics are unobservable through the production entry point.
/// This seam is what lets a planted registry exercise them -- the only way a
/// guard whose population has been driven to zero can be checked at all.
fn carve_out_in<'a>(rows: &'a [CorpusCarveOut], name: &str) -> Option<&'a CorpusCarveOut> {
    rows.iter().find(|row| row.declaration == name)
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
    /// Rejection triage (bead `franken_lean-t6r7`), keyed by the kernel's OWN
    /// outcome token — `rejected:BlockMismatch`, `inconclusive:Steps` — and not
    /// by a family name parsed back out of a rendered message. The token is the
    /// structured `UnitOutcome::outcome` field the verdict stream is built from,
    /// so the census cannot disagree with the verdict it is counting, and a new
    /// rejection class names itself here without anyone extending a match arm.
    ///
    /// Two maps rather than one because the two populations answer different
    /// questions: `restrictive_families` triages rows the Reference ACCEPTED and
    /// we did not, which is the D23 direction this lane exists to bound;
    /// `no_answer_families` triages rows we could not answer for at all, which
    /// are unscorable and say nothing about kernel completeness. Folding them
    /// together would let an exhaustion budget read as a kernel divergence.
    restrictive_families: BTreeMap<String, u64>,
    no_answer_families: BTreeMap<String, u64>,
}

/// The two non-answer families that name a CONTEXT-construction failure rather
/// than a kernel outcome. Spelled once because the scorer writes them and the
/// guard reasons about them, and a typo in either place would silently create a
/// third family that no one is counting.
const FAMILY_NO_DECLARATION_ENVELOPE: &str = "context:subject_has_no_declaration_envelope";
const FAMILY_UNFAITHFUL_IMPORT_CONTEXT: &str =
    "context:import_context_not_faithfully_representable";

/// Which side of the D23 split a family census describes. The two are not
/// interchangeable and the token itself says which it belongs to.
#[derive(Clone, Copy, PartialEq, Eq)]
enum FamilyDirection {
    Restrictive,
    NoAnswer,
}

impl FamilyDirection {
    fn field(self) -> &'static str {
        match self {
            FamilyDirection::Restrictive => "restrictive_families",
            FamilyDirection::NoAnswer => "no_answer_families",
        }
    }
}

/// Everything a family token must be, stated once for the producer and the
/// reader (bead `franken_lean-t6r7`).
///
/// **The counts were bound; the NAMES were not.** `validate` already refused a
/// census that did not sum to the buckets it described, so a token could be any
/// string at all -- `banana=14` satisfied every law. That is the same shape as
/// `ci/BOUNDARY_API.txt`'s discarded no-admission argument recorded in AGENTS.md:
/// a field checked for presence and then never read.
///
/// **The two rules, and why each is derivable rather than invented.**
///
/// 1. DELIMITER SAFETY. The receipt serializes a census as `token=count` joined
///    by `,`. A token containing either delimiter would be re-read as a
///    different token with a different count, silently -- `rsplit_once('=')`
///    would take the wrong `=`, and a comma would split one entry into two. No
///    token produced today contains either (every one is `rejected:<unit enum
///    variant>`, `inconclusive:<cause>`, `internal_fault`, or a `context:`
///    reason), so this rule costs nothing now and is what keeps the format
///    honest when a future `RejectClass` grows a payload whose `Debug` rendering
///    carries `{ field: value, other: value }`.
///
/// 2. DIRECTION. `subject_axis` sends an outcome to `Rejected` if and only if
///    its token starts with `rejected:`, and to `NoAnswer` otherwise. So every
///    restrictive family key starts with `rejected:` and no non-answer key ever
///    does -- not by convention but by the one branch that routes them. A
///    restrictive row triaged to `inconclusive:Steps` would mean a rejection and
///    an exhaustion had been counted as the same thing, which is the single
///    confusion this census was split in two to prevent.
fn check_family_token(family: &str, direction: FamilyDirection) -> Result<(), String> {
    let field = direction.field();
    if family.is_empty() {
        return Err(format!("`{field}` carries an entry that names no family"));
    }
    for delimiter in [',', '='] {
        if family.contains(delimiter) {
            return Err(format!(
                "`{field}` family `{family}` contains the `{delimiter}` this format uses as a \
                 delimiter; the row would be re-read as a different family with a different count"
            ));
        }
    }
    let rejected = family.starts_with("rejected:");
    match direction {
        FamilyDirection::Restrictive if !rejected => Err(format!(
            "`{field}` family `{family}` is not a `rejected:` token, but a restrictive row is by \
             definition one the subject REJECTED; counting it here would merge a rejection with a \
             non-answer"
        )),
        FamilyDirection::NoAnswer if rejected => Err(format!(
            "`{field}` family `{family}` is a `rejected:` token, but a non-answer is precisely an \
             outcome that is not a rejection; it says nothing about kernel completeness and must \
             not be counted as if it did"
        )),
        FamilyDirection::NoAnswer if family == "accepted" => Err(format!(
            "`{field}` family `{family}` is the ACCEPTED token; an accepted row is neither \
             unscorable nor a non-answer"
        )),
        _ => Ok(()),
    }
}

/// Add retained-row counts without trusting them to be addable.
///
/// **A `Result` that panics is not a `Result`.** `validate` promises to REFUSE a
/// bad row; the retained file is append-only and editable by hand, so its
/// numbers are attacker-controlled in the only sense that matters here. Two
/// fields near `u64::MAX` make an unchecked `+` overflow, and in a debug build
/// -- which is how these tests run -- that ABORTS. The guard would then die with
/// "attempt to add with overflow" instead of saying the row does not conserve:
/// a panic where a refusal was promised, and a diagnosis pointing at arithmetic
/// rather than at the row.
///
/// The label is carried so the refusal says WHICH sum overflowed, since several
/// of them add attacker-supplied numbers.
fn checked_sum(what: &str, values: &[u64]) -> Result<u64, String> {
    let mut total: u64 = 0;
    for value in values {
        total = total.checked_add(*value).ok_or_else(|| {
            format!(
                "`{what}` overflows a u64 in this row. A retained receipt is editable by hand, so \
                 its counts are not to be trusted into arithmetic"
            )
        })?;
    }
    Ok(total)
}

/// Assert a token is refused in `direction`, and refused for the REASON named.
///
/// **Why not `is_err()`.** `check_family_token` can refuse for four different
/// reasons: an empty name, either delimiter, the wrong direction, or the
/// ACCEPTED token. A bare `is_err()` cannot tell them apart, so it keeps passing
/// if the rule under test stops working and some other rule refuses the token
/// instead -- which is how a direction check would go dark while every call site
/// stayed green. Every refusal assertion on these tokens goes through here so
/// that cannot happen quietly.
fn assert_family_token_refused(token: &str, direction: FamilyDirection, because: &str) {
    let field = direction.field();
    let reason = match check_family_token(token, direction) {
        Ok(()) => panic!("`{token}` was accepted as a `{field}` entry"),
        Err(reason) => reason,
    };
    // `contains("")` IS ALWAYS TRUE. An empty `because` would turn this helper
    // into `is_err()` -- exactly the check it was written to replace -- and every
    // caller would keep passing while naming no rule at all. Refused at the door
    // so the helper cannot be silently disabled by its own argument.
    assert!(
        !because.is_empty(),
        "`{token}`: a refusal must be checked against a NAMED rule; an empty expectation matches \
         every message"
    );
    assert!(
        reason.contains(because),
        "`{token}` was refused as a `{field}` entry, but not for `{because}`: {reason}"
    );
}

/// Render a family census in the receipt's canonical form: `token=count`,
/// ascending by token (the `BTreeMap` order), so two runs that saw the same
/// families produce byte-identical rows.
fn family_census_rows(census: &BTreeMap<String, u64>) -> Vec<String> {
    census
        .iter()
        .map(|(family, count)| format!("{family}={count}"))
        .collect()
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
        for (family, count) in &other.restrictive_families {
            *self.restrictive_families.entry(family.clone()).or_default() += count;
        }
        for (family, count) in &other.no_answer_families {
            *self.no_answer_families.entry(family.clone()).or_default() += count;
        }
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
        // THE UNSCORABLE SPLIT. `unscorable` is only ever incremented alongside
        // one of these two, so this holds by construction at every write site --
        // which is exactly why it is worth stating. It is the ONLY thing that
        // binds `oracle_skipped`: without it that field is a free number, and a
        // receipt could carry any value at all for "how much the oracle would
        // not answer for" while every other law still balanced.
        assert_eq!(
            self.unscorable,
            self.oracle_skipped + self.subject_no_answer,
            "{scope}: unscorable rows must split into oracle skips and subject non-answers"
        );
        // THE TRIAGE IS TOTAL, OR IT IS NOT A TRIAGE. `franken_lean-t6r7` asks
        // that every rejection land in a NAMED family; a census that counted
        // fewer rows than the buckets it describes would publish a partial
        // triage wearing the shape of a complete one, and the shortfall would
        // be invisible in the summary because both numbers are printed
        // separately and neither is derived from the other.
        for (family, direction) in self
            .restrictive_families
            .keys()
            .map(|family| (family, FamilyDirection::Restrictive))
            .chain(
                self.no_answer_families
                    .keys()
                    .map(|family| (family, FamilyDirection::NoAnswer)),
            )
        {
            if let Err(reason) = check_family_token(family, direction) {
                panic!("{scope}: {reason}");
            }
        }
        assert_eq!(
            self.restrictive_families.values().sum::<u64>(),
            self.restrictive_with_carve_out + self.restrictive_without_carve_out,
            "{scope}: every restrictive row must be triaged to exactly one family"
        );
        assert_eq!(
            self.no_answer_families.values().sum::<u64>(),
            self.subject_no_answer,
            "{scope}: every subject non-answer must be triaged to exactly one family"
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
                    // Triage from the structured outcome token, never from the
                    // rendered `ours` message (bead `franken_lean-t6r7`).
                    *counts
                        .restrictive_families
                        .entry(outcome.outcome.clone())
                        .or_default() += 1;
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
                *counts
                    .no_answer_families
                    .entry(outcome.outcome.clone())
                    .or_default() += affected;
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
        // A row our side never produced an admission envelope for is a
        // non-answer with a NAMED cause, not an untyped remainder. The family
        // token is the same typed reason the finding below prints, under a
        // `context:` prefix so a reader can tell a kernel outcome token
        // (`rejected:`, `inconclusive:`) from a context-construction reason.
        *counts
            .no_answer_families
            .entry(FAMILY_NO_DECLARATION_ENVELOPE.to_string())
            .or_default() += subject_omitted.len() as u64;
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
    // THE DIRECTORY CASE NOW STOPS EARLIER THAN IT USED TO, and the expectation
    // follows the product rather than the product following the expectation.
    // `check-olean` gained a set-wide declaration scan (`fln/src/lib.rs`,
    // `ConflictingModuleDeclaration`) that runs BEFORE closed-set import
    // planning. Two modules in this directory decode to different declarations
    // sharing a name, so the run is refused there and never reaches the
    // unresolved-imports refusal this line used to observe. Both classes exit 1,
    // which is why the exit-code assertion above kept passing while this one
    // failed.
    //
    // THE DETAIL IS ASSERTED, NOT ONLY THE CLASS, and that is the whole care
    // taken here. `declaration-closure` is a BUCKET: `MissingConstants` and
    // `DuplicateDeclaration` share it, and both are exactly the companion-
    // association failures this test exists to catch. Widening the expectation to
    // the class alone would have made this line accept the defect it guards.
    // Matching the conflict's own rendering keeps the two apart.
    assert!(
        directory_cli
            .stderr
            .contains("\"class\":\"declaration-closure\""),
        "directory collection must be refused by the set-wide declaration scan: {}",
        directory_cli.stderr
    );
    assert!(
        directory_cli
            .stderr
            .contains("decode to different declarations both named"),
        "the refusal must be the set-wide NAME CONFLICT specifically. `MissingConstants` and \
         `DuplicateDeclaration` carry the same class and would mean a companion part was lost or \
         doubled, which is the regression this test is here to catch: {}",
        directory_cli.stderr
    );
    // Unchanged, and it is this line -- not the class -- that actually witnesses
    // companion pairing: a directory collection that failed to associate a
    // module with its parts would complain about a missing `.olean`.
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
            assert_field_once(row, key, &needle)?;
            let start = row
                .find(&needle)
                .ok_or_else(|| format!("missing string field `{key}`"))?
                + needle.len();
            let rest = &row[start..];
            let end = rest
                .find('"')
                .ok_or_else(|| format!("unterminated string field `{key}`"))?;
            let value = &rest[..end];
            assert_no_escape(key, value)?;
            assert_string_terminator(key, rest, end)?;
            Ok(value.to_string())
        }
        fn number(row: &str, key: &str) -> Result<u64, String> {
            let needle = format!("\"{key}\":");
            assert_field_once(row, key, &needle)?;
            let start = row
                .find(&needle)
                .ok_or_else(|| format!("missing numeric field `{key}`"))?
                + needle.len();
            let rest = &row[start..];
            let end = rest
                .find(|c: char| !c.is_ascii_digit())
                .unwrap_or(rest.len());
            assert_number_terminator(key, rest, end)?;
            rest[..end]
                .parse()
                .map_err(|_| format!("field `{key}` is not a u64"))
        }
        fn array<'a>(row: &'a str, key: &str) -> Result<&'a str, String> {
            let needle = format!("\"{key}\":[");
            assert_field_once(row, key, &needle)?;
            let start = row
                .find(&needle)
                .ok_or_else(|| format!("missing array field `{key}`"))?
                + needle.len();
            let rest = &row[start..];
            let end = rest
                .find(']')
                .ok_or_else(|| format!("unterminated array field `{key}`"))?;
            assert_array_terminator(key, rest, end)?;
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
        // TRIMMED, LIKE `bead` AND `target` TWO RULES DOWN. This was
        // `is_empty()`, so a hash of spaces named no corpus revision and passed
        // anyway -- the exact thing the message below says it refuses. A
        // retained row is editable by hand, which is why this file already
        // refuses to trust its numbers into arithmetic; a blank field is the
        // same threat wearing a different shape.
        if self.corpus_fixture_hash.trim().is_empty() {
            return Err(
                "row carries an empty corpus_fixture_hash, so it names no corpus revision"
                    .to_string(),
            );
        }
        // A NAME IS NOT A DIGEST, AND THIS FIELD IS THE ONLY HANDLE ON WHICH
        // CORPUS WAS OBSERVED. Emptiness was refused; SHAPE was not, so a row
        // could identify its corpus revision as `mathlib` or `latest` and pass
        // every check here. Measured before adding it: the committed hash
        // appears NOWHERE else in the tree -- `git grep` finds it only in this
        // receipt and one bead -- so nothing downstream would ever contradict a
        // label. `SUITE.lock` pins the corpus at a commit, but the receipt
        // carries no corpus-commit field, so a real BINDING is not available
        // without the corpus in the tree. Requiring the field to BE a digest is
        // the strongest check this file can make on its own, and it is a check
        // on the field's kind rather than on its value.
        //
        // 64 lowercase hex, measured from the committed row and from the
        // producer, which fills this from the inventory's own fixture hash. The
        // width is pinned deliberately: a digest of a different width is a
        // digest of a different thing.
        //
        // NOT applied to the sibling receipt type, which carries the same field
        // with the same emptiness-only rule: ten fixtures in this file give it a
        // LABEL on purpose, so tightening it is a real change to those guards
        // rather than a rule added beside them. Disclosed rather than done.
        if self.corpus_fixture_hash.len() != 64
            || !self
                .corpus_fixture_hash
                .chars()
                .all(|character| matches!(character, '0'..='9' | 'a'..='f'))
        {
            return Err(format!(
                "row names its corpus revision as `{}`, which is not a 64-character lowercase \
                 hex digest. This field is the only record of WHICH corpus was observed, and a \
                 label cannot be checked against anything",
                self.corpus_fixture_hash
            ));
        }
        if self.lane_source_digest_at_run.trim().is_empty() {
            return Err(
                "row carries an empty lane_source_digest_at_run, so it names no producing \
                 source"
                    .to_string(),
            );
        }
        // AND THE SAME KIND CHECK AS THE CORPUS HASH, ONE FIELD DOWN. This
        // records WHICH lane source produced the row, and emptiness was the only
        // rule: `hand-run`, `the-lane` or `v1` would all pass as provenance.
        // Measured 64 lowercase hex on the committed row, from a producer that
        // digests the lane's own source.
        //
        // WHAT THIS FIELD CANNOT BE BOUND TO, AND THE NUMBER IS THE ARGUMENT.
        // The producer hashes `include_str!("kernel_replay.rs")` -- this whole
        // file. 165 commits have touched it since the observation was taken, so
        // the recorded digest has been stale for 165 commits and this cell makes
        // it 166. Comparing it against the current source would redden
        // permanently and be bypassed, which is the failure the PG-5 waiver's
        // own doc-comment prices and rejects for the invalidating cone. The
        // field is provenance BY RECORD, never a check, and saying so here stops
        // a later reader from "finishing" it into a wall.
        if self.lane_source_digest_at_run.len() != 64
            || !self
                .lane_source_digest_at_run
                .chars()
                .all(|character| matches!(character, '0'..='9' | 'a'..='f'))
        {
            return Err(format!(
                "row names its producing source as `{}`, which is not a 64-character lowercase \
                 hex digest. A label records nothing a later reader could resolve to a source",
                self.lane_source_digest_at_run
            ));
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
    std::env::var_os(MATHLIB_CORPUS_ROOT_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(DEFAULT_MATHLIB_CORPUS_ROOT))
}

/// The host path the whole-Mathlib lane requires when nothing overrides it, and
/// the variable that overrides it.
///
/// These are the PRODUCTION spellings.
/// `the_corpus_root_is_exactly_the_documented_host_path` writes the same path out
/// again as a literal and compares. That duplication is deliberate and is the
/// only reason the comparison means anything: a test that reused these constants
/// would agree with any value they ever held, including a wrong one. One side is
/// the implementation, the other is the specification, and they must be written
/// independently or the check is a mirror.
const DEFAULT_MATHLIB_CORPUS_ROOT: &str = "/data/tmp/mathlib4-corpus";
const MATHLIB_CORPUS_ROOT_ENV: &str = "FLN_MATHLIB_CORPUS";

/// Refuse before an expensive whole-corpus run when its external input cannot
/// identify itself. This is intentionally stronger than `is_dir()`: a different
/// Mathlib commit, a symlinked checkout, or a source-only checkout would make a
/// seemingly successful sweep evidence about the wrong world.
fn preflight_mathlib_corpus() -> Result<PathBuf, String> {
    preflight_mathlib_corpus_at(&mathlib_corpus_root())
}

/// The same gate over an explicitly named root, so a test can hand it something
/// other than this host's corpus. Without this seam the classifier below could
/// only ever be exercised against whatever happens to be on the machine, and on
/// a machine with no corpus that means one arm of three.
fn preflight_mathlib_corpus_at(root: &Path) -> Result<PathBuf, String> {
    let corpus = root.to_path_buf();
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

/// How the whole-Mathlib corpus input presents itself on THIS host, as a typed
/// value rather than as a boolean.
///
/// The distinction that matters is between ABSENT and MISPROVISIONED, and
/// collapsing them is the reason this enum exists. A corpus that is not there is
/// a missing host input: nothing in the repository can fix it, and a red for it
/// is a red nobody can clear. A corpus that IS there and is the wrong thing -- a
/// symlink, another Mathlib revision, a source-only checkout with no built
/// oleans -- is a misprovisioned input, and skipping THAT would let someone
/// provision the wrong corpus and read the resulting green as coverage.
enum MathlibCorpusInput {
    Absent { root: PathBuf, detail: String },
    Present { root: PathBuf, library: PathBuf },
    Misprovisioned { root: PathBuf, reason: String },
}

impl MathlibCorpusInput {
    /// Whether this classification makes the walk SKIP.
    ///
    /// Exactly one of the three does, and that is the law: a skip is earned by
    /// the root not being on this host, and by nothing else. A present root that
    /// cannot identify itself as the pinned corpus is a misprovisioned input and
    /// fails; a present root that can is walked. Neither is quietly passed over.
    fn skips(&self) -> bool {
        matches!(self, MathlibCorpusInput::Absent { .. })
    }

    /// The root this classification is ABOUT, so a caller can check the answer
    /// is about the path it asked after rather than some other path.
    fn root(&self) -> &Path {
        match self {
            MathlibCorpusInput::Absent { root, .. }
            | MathlibCorpusInput::Present { root, .. }
            | MathlibCorpusInput::Misprovisioned { root, .. } => root,
        }
    }
}

fn classify_mathlib_corpus_input() -> MathlibCorpusInput {
    classify_mathlib_corpus_input_at(mathlib_corpus_root())
}

fn classify_mathlib_corpus_input_at(root: PathBuf) -> MathlibCorpusInput {
    match fs::symlink_metadata(&root) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => MathlibCorpusInput::Absent {
            detail: format!("{} does not exist: {error}", root.display()),
            root,
        },
        Err(error) => MathlibCorpusInput::Misprovisioned {
            reason: format!("cannot inspect {}: {error}", root.display()),
            root,
        },
        // Present on disk: now it must prove it is the PINNED corpus. Every
        // rejection `preflight_mathlib_corpus` can return is a misprovisioning,
        // because the path existing is what separates the two arms.
        Ok(_) => match preflight_mathlib_corpus_at(&root) {
            Ok(library) => MathlibCorpusInput::Present { root, library },
            Err(reason) => MathlibCorpusInput::Misprovisioned { root, reason },
        },
    }
}

/// What one inventory walk observed: the built olean set and the canonical
/// module names it projects to.
struct OleanInventory {
    oleans: Vec<PathBuf>,
    modules: Vec<String>,
}

/// Enumerate a built olean tree and project it to canonical module names,
/// checking the two properties that hold for ANY such tree.
///
/// **Why this is a function and not four assertions inside the walk.** Every
/// property below was previously asserted inline in the corpus walk, which can
/// only execute on a host that has the corpus -- and no host has it. So the
/// checks were written but unreachable, and "unreachable" and "correct" look
/// identical from here. Taking a library root as a parameter is what lets a
/// three-file fixture drive the same code, including its failure.
///
/// It returns `Err` rather than panicking for the same reason: a control has to
/// be able to assert that a bad tree is REFUSED, and an assertion inside cannot
/// be caught.
///
/// This reads no file contents. It stats, filters by extension, and joins path
/// components; decoding is the `#[ignore]`d sweep's job.
fn walk_olean_inventory(
    library: &Path,
    module_prefix: Option<&str>,
) -> Result<OleanInventory, String> {
    let mut oleans = Vec::new();
    collect_present_oleans(library, &mut oleans)?;
    // REDUNDANT AND KEPT. `collect_present_oleans` already emits paths in this
    // exact order -- a depth-first walk with entries sorted by file name within
    // each directory produces precisely the global path order, measured, because
    // component-wise path comparison IS lexicographic order on the component
    // sequence. Deleting this line changes nothing observable, so no test can
    // kill it; it stays because the order is what this function GUARANTEES to
    // its caller, and that guarantee should not depend on a helper's internal
    // choice. Said plainly so a mutation campaign records it as inert rather
    // than as a surviving mutant somebody ought to chase.
    oleans.sort();
    // ONE TRAVERSAL, NOT TWO. This used to call `module_names_below`, which
    // walks the tree AGAIN from the same root and re-sorts what it finds. The
    // two vectors then came from two `read_dir` sweeps at different moments, and
    // the comment below claimed their lengths "always agree" -- true of a tree
    // nobody is writing to, and this suite has no test that walks a fixture
    // another test is building. It was unreachable because of the test
    // population, not because two traversals of one root must agree.
    //
    // Projecting the paths already collected removes the window and makes the
    // parallel correspondence structural: `modules[i]` is now the projection of
    // `oleans[i]` because it is built from it, not because two independent
    // enumerations happen to sort the same way.
    let modules = oleans
        .iter()
        .map(|path| {
            module_name_from_path(library, path)
                .map(|relative| qualify_module_name(module_prefix, relative))
        })
        .collect::<Result<Vec<String>, String>>()?;

    // DEFENSIVE, AND NOW IMPOSSIBLE RATHER THAN MERELY UNOBSERVED. `modules` is
    // a `map` over `oleans`, so the lengths cannot differ without the iterator
    // protocol being wrong. It stays because the guard costs nothing and states
    // what the two vectors mean to each other; a mutation campaign should record
    // it as inert, not chase it.
    if modules.len() != oleans.len() {
        return Err(format!(
            "{} olean(s) below {} produced {} module name(s); the enumeration and the projection \
             disagree about the population",
            oleans.len(),
            library.display(),
            modules.len()
        ));
    }
    // ALSO DEFENSIVE, for a reason that is checked rather than assumed:
    // `qualify_module_name` prepends `{prefix}.` unconditionally, so every name
    // it returns starts with the prefix and this branch cannot fire on input.
    // That premise is pinned by
    // `qualification_prepends_unconditionally_which_is_why_the_walk_guard_is_defensive`;
    // if it ever stops holding, this guard becomes live and that test goes red
    // first, which is the order those two should fail in.
    if let Some(prefix) = module_prefix {
        let qualified = format!("{prefix}.");
        if let Some(unqualified) = modules.iter().find(|name| !name.starts_with(&qualified)) {
            return Err(format!(
                "module `{unqualified}` is not qualified with `{prefix}`; an unqualified name \
                 cannot be matched against the imports recorded inside an olean"
            ));
        }
    }
    // THE PROJECTION MUST BE INJECTIVE. `path -> module name` is a projection,
    // and a projection used as an identity without anyone checking injectivity
    // is a defect this repository has already found seven times. It is
    // constructible here rather than theoretical: `A/B.olean` and `A.B.olean`
    // both project to `A.B`, so two real files can collapse to one name, the
    // inventory silently under-counts, and the shortfall looks exactly like a
    // smaller corpus.
    //
    // THE REFUSAL NAMES THE COLLISION, AND IT USED TO ONLY COUNT IT. The message
    // was two numbers -- so many oleans, so many distinct names -- which on the
    // corpus this walk exists for reads as "5000 olean(s) projected to 4999
    // distinct module name(s)" and gives whoever has to fix it a subtraction and
    // no lead. The one place this guard can fire for real is the one place a
    // by-hand search through the population is hopeless.
    //
    // The grouping is legitimate because `modules[i]` IS the projection of
    // `oleans[i]`: two separate walks, related by nothing but construction, and
    // pinned by
    // `the_inventory_vectors_are_parallel_and_the_extension_match_is_exact`. If
    // that correspondence ever breaks, this message starts blaming the wrong
    // files, which is why it is pinned there rather than assumed here.
    let mut by_name: BTreeMap<&str, Vec<&Path>> = BTreeMap::new();
    for (name, path) in modules.iter().zip(&oleans) {
        by_name
            .entry(name.as_str())
            .or_default()
            .push(path.as_path());
    }
    let collisions = by_name
        .iter()
        .filter(|(_, paths)| paths.len() > 1)
        .collect::<Vec<_>>();
    if !collisions.is_empty() {
        // BOUNDED, AND THE BOUND IS DISCLOSED. A message carrying every
        // collision on a corpus-scale tree is unreadable, but a cap that says
        // nothing about what it dropped reads as a complete list -- the failure
        // mode where a scan that skips what it cannot handle silently redefines
        // its own denominator. Whatever is not shown is counted out loud.
        const SHOWN: usize = 3;
        let mut detail = String::new();
        for (name, paths) in collisions.iter().take(SHOWN) {
            if !detail.is_empty() {
                detail.push_str("; ");
            }
            detail.push_str(&format!("`{name}` <- {paths:?}"));
        }
        if collisions.len() > SHOWN {
            detail.push_str(&format!(
                "; and {} more colliding name(s) not listed",
                collisions.len() - SHOWN
            ));
        }
        return Err(format!(
            "{} olean(s) below {} projected to {} distinct module name(s); the module name is \
             being used as an identity and it is not injective over this tree. {} name(s) \
             collide: {detail}",
            oleans.len(),
            library.display(),
            by_name.len(),
            collisions.len()
        ));
    }
    Ok(OleanInventory { oleans, modules })
}

/// Build a tiny olean tree for the inventory controls.
///
/// **Empty files are the right fixture here.** `walk_olean_inventory` stats,
/// filters by extension and joins path components; it never opens a file. A
/// fixture with real olean bytes would suggest this exercises decoding, which it
/// does not and must not -- decoding the corpus is the `#[ignore]`d sweep.
///
/// **Nothing is deleted.** The tree is written under `CARGO_TARGET_TMPDIR`,
/// which Cargo provides per test target and which lives inside the ignored
/// `target/` directory, never the source tree. Files are created or truncated,
/// never removed, so a run leaves no removal behind and needs no cleanup rights.
/// Because stale entries are therefore never swept, each fixture shape carries a
/// version in its directory name: CHANGE THE SHAPE, BUMP THE NAME, or a previous
/// run's leftovers join the population and the counts below stop meaning what
/// they say.
fn write_inventory_fixture(versioned_name: &str, relative_files: &[&str]) -> PathBuf {
    write_inventory_fixture_with(versioned_name, relative_files, |path| fs::write(path, b""))
}

/// The same writer with its per-entry WRITE as a parameter, so the order of
/// "record the shape" against "build the tree" can be observed.
///
/// Nothing about a successful build distinguishes the two orders: the tree and
/// the record are both there either way. The difference only shows when the
/// build dies partway, and a caller can produce that on demand by handing over a
/// write that fails. Production passes `fs::write` one line above.
fn write_inventory_fixture_with(
    versioned_name: &str,
    relative_files: &[&str],
    mut write_entry: impl FnMut(&Path) -> std::io::Result<()>,
) -> PathBuf {
    // AND THE NAME ITSELF WAS NEVER CHECKED, WHICH IS THE MORE DANGEROUS HALF.
    // Every entry below is validated three ways; `versioned_name` was joined
    // straight onto the temporary directory and formatted into the shape
    // record's path with nothing looking at it. It decides WHERE all of that
    // goes, so it is the argument that can do the most damage.
    //
    // An empty name makes `base` the temporary directory itself -- the directory
    // every fixture in this file already sits in, side by side, measured on a
    // batch run's tree. The fixture's population would silently become all of
    // them: the union hazard the registry and the shape record exist to prevent,
    // arriving through the one parameter neither of them inspects. (Cargo
    // documents this directory as per-PACKAGE, so other integration-test
    // binaries would share it too; I have not observed one here, so the argument
    // rests on the fixtures in this file, which is already enough.) A `..`
    // climbs out into `target/`. A separator nests the tree while leaving the
    // shape record beside a directory that is no longer its parent.
    //
    // Three distinct reasons, because a single "bad fixture name" would let any
    // of the three pass in another's place.
    //
    // AND IT MUST BE THE NAME, NOT MERELY PARSE AS ONE. The rule above reads the
    // name as a PATH; the shape record is built from it as a STRING, with
    // `format!("{versioned_name}.manifest")`. `Spelled/` satisfies the path
    // reading -- one `Normal` component -- and the two uses then disagree:
    // `join` gives the tree `<tmp>/Spelled`, while the format gives
    // `<tmp>/Spelled/.manifest`, which is INSIDE that tree rather than beside
    // it. Measured, both halves.
    //
    // A record inside the tree joins every walk of it, which is what the
    // sibling-path assertion in the manifest test exists to prevent. Worse,
    // `Spelled` and `Spelled/` are the same tree -- `Path` equality is by
    // components -- but different registry keys and different record paths, so
    // the two guards that exist to catch two fixtures sharing one tree each see
    // two unrelated fixtures.
    let name_fault = {
        let mut components = Path::new(versioned_name).components();
        match (components.next(), components.next()) {
            (Some(std::path::Component::Normal(name)), None)
                if name == std::ffi::OsStr::new(versioned_name) =>
            {
                None
            }
            (Some(std::path::Component::Normal(_)), None) => Some(
                "reads as one ordinary component but is not spelled as one, so the tree is \
                 joined from the path and the shape record is formatted from the string, and \
                 the two land in different places",
            ),
            (None, _) => Some(
                "names nothing at all, so the fixture tree would BE the shared temporary \
                 directory and its population would be every other fixture in this package",
            ),
            (Some(std::path::Component::Normal(_)), Some(_)) => Some(
                "holds a path separator, so the tree would nest while the shape record stayed \
                 beside a directory that is no longer its parent",
            ),
            (Some(_), _) => Some(
                "is not an ordinary name, so it can climb out of the temporary directory \
                 altogether",
            ),
        }
    };
    if let Some(fault) = name_fault {
        panic!("fixture name `{versioned_name}` {fault}");
    }

    // THE RECORD'S SUFFIX IS RESERVED, BECAUSE A TREE AND A RECORD SHARE ONE
    // DIRECTORY. The shape record for `X` is `<tmp>/X.manifest`, which is
    // exactly where a fixture NAMED `X.manifest` would put its tree. Both names
    // pass every rule above -- each is one ordinary component, spelled as one --
    // and the two objects then fight over one path.
    //
    // Which failure you get depends on build order, which is the tell that this
    // is a naming problem and not a filesystem one. Build `X` first and the
    // record is a file, so the other fixture's `create_dir_all` dies with a raw
    // `Not a directory`. Build `X.manifest` first and the record path is a
    // directory, so `X`'s record read fails and is refused as unreadable -- true,
    // and pointing at the wrong cause.
    //
    // A STRING SUFFIX IS THE RIGHT SUBJECT HERE, unlike everywhere else in this
    // function. The record path is FORMATTED from the name, so what collides is
    // the spelling, not a path component.
    assert!(
        !versioned_name.ends_with(".manifest"),
        "fixture name `{versioned_name}` ends with the suffix the shape record uses, so this \
         fixture's TREE would sit exactly where another fixture's record does. Which of the two \
         fails, and how, would depend on which was built first"
    );

    // `relative_files` IS A PROMISE THE PARAMETER'S NAME MAKES AND NOTHING KEPT.
    // `Path::join` obeys the caller, not the name: an entry beginning with `/`
    // DISCARDS the base entirely and lands wherever it says -- outside
    // `CARGO_TARGET_TMPDIR`, outside `target/`, anywhere -- and a `..` entry
    // climbs out of this tree into a SIBLING fixture's, where it would add a
    // file to a test that never mentioned it and move a count nobody can trace
    // back here.
    //
    // The registry below cannot see that collision: the two fixtures have
    // different names and share only a file. Neither can the obvious guard --
    // `base.join("../x").starts_with(base)` is TRUE, because `..` is an ordinary
    // component to a lexical prefix test and nothing resolves it. So the check
    // is on the COMPONENTS of the entry, which is the only place the escape is
    // visible before it happens.
    //
    // On components, NOT on the substring `..`. `Dotted/x..olean` is a real
    // fixture entry in this file whose components are both `Normal`; a substring
    // test would refuse it and would be refusing a legitimate tree.
    //
    // Before the lock, deliberately: a panic while the guard is alive would
    // poison the Mutex and take every later fixture in the process down with it.
    for relative in relative_files {
        assert!(
            Path::new(relative)
                .components()
                .all(|component| matches!(component, std::path::Component::Normal(_))),
            "fixture entry `{relative}` is not a plain relative path. Every component must be an \
             ordinary name: a leading `/` discards the fixture base and writes outside the target \
             directory, and a `..` writes into a sibling fixture's tree, where the file joins \
             another test's population and moves a count that has nothing to do with this fixture"
        );
    }

    // THE LIST IS A SET, AND NOTHING MADE IT ONE. `fs::write` creates or
    // truncates, so an entry named twice produces ONE file: the tree comes out
    // smaller than the list that built it. Every fixture test here takes its
    // expected count from that list -- `oleans.len() == CREATED.len()` in the
    // sorted and helper-order tests, a literal `3` or `4` elsewhere -- so the
    // duplicate surfaces as "the walk must enumerate exactly N files", accusing
    // the walk of losing a file that was never written. A repeated line in a
    // hand-written list is an ordinary copy-paste slip; being told which line it
    // is beats re-deriving it from a count that is off by one.
    //
    // It also poisons the shape record beside the tree: the manifest would store
    // the entry twice, so a later run that tidied the list to one copy would be
    // refused as a shape change that never happened.
    //
    // KEYED ON THE PATH, NOT ON THE STRING, AND IT USED TO BE THE STRING. Two
    // spellings of one path are two different `&str`s: `A.olean` and `A.olean/`
    // differ by a trailing separator, `A/B.olean` and `A//B.olean` by a repeated
    // one. `Path` drops both when it splits into components, so `base.join`
    // returns the SAME file for either -- measured, not assumed -- and a set of
    // strings sees two entries where the filesystem sees one. The guard let
    // through exactly the case it exists to catch, because it compared a
    // rendering instead of the thing rendered.
    {
        let mut seen: BTreeMap<Vec<std::ffi::OsString>, &str> = BTreeMap::new();
        for relative in relative_files {
            let key = Path::new(relative)
                .components()
                .map(|component| component.as_os_str().to_owned())
                .collect::<Vec<_>>();
            if let Some(previous) = seen.insert(key, *relative) {
                panic!(
                    "fixture `{versioned_name}` lists `{previous}` and `{relative}`, which name \
                     the same file. The second write truncates the first, so the tree holds one \
                     file where the list names two and every count taken from the list is one \
                     too many"
                );
            }
        }
    }

    // ONE ENTRY CANNOT BE BOTH A FILE AND THE DIRECTORY ABOVE ANOTHER. Listing
    // `Nested` beside `Nested/Leaf.olean` asks for a path to be a file and a
    // directory at once, and the writer discovers that from the operating system
    // -- in one of two different ways, depending which entry it reaches first.
    // Written in this order it dies in `create_dir_all` with `Not a directory`;
    // written in the other it dies in `fs::write` with `Is a directory`. Two
    // messages for one authoring mistake, chosen by list order, and neither
    // names the OTHER entry -- which is the only thing the reader actually needs.
    //
    // Refused here so the diagnosis is the same either way and names both. This
    // is sound only because the guard above already required every component to
    // be `Normal`: `Path::starts_with` is a component-wise prefix test that does
    // not resolve `..`, so a `..` entry could otherwise sit below another
    // lexically while pointing somewhere else entirely.
    for outer in relative_files {
        for inner in relative_files {
            let outer_depth = Path::new(outer).components().count();
            let inner_depth = Path::new(inner).components().count();
            assert!(
                !(outer_depth < inner_depth && Path::new(inner).starts_with(Path::new(outer))),
                "fixture `{versioned_name}` lists `{outer}`, which is written as a file, and \
                 `{inner}`, which needs `{outer}` to be a directory. One path cannot be both, so \
                 the build fails in the filesystem with a message that names only whichever of \
                 the two it reached second"
            );
        }
    }

    // TWO TESTS SHARING A NAME IS INVISIBLE UNTIL IT CORRUPTS A COUNT. Nothing
    // removes these trees, so a second build under the same name UNIONS into the
    // first: one test's walk then sees the other's files, its census comes out
    // wrong, and the failure surfaces as an unexplained count in whichever test
    // the interleaving happened to disadvantage. Tests run in parallel, so which
    // one that is need not be stable between runs.
    //
    // The rule until now was a comment asking whoever adds a fixture to pick a
    // fresh name. This makes it mechanical, and names BOTH file sets when it
    // fires so the collision is obvious rather than merely reported.
    //
    // Per PROCESS, deliberately: this one is about two tests fighting over a
    // name inside one run. The cross-run half -- a tree left by an EARLIER run
    // with a different shape, which the next run then unions into -- used to be
    // this comment's problem to describe and the reader's problem to remember.
    // It is now the manifest's, below.
    static CLAIMED: OnceLock<Mutex<BTreeMap<String, Vec<String>>>> = OnceLock::new();
    // ONE CANONICAL FORM, USED BY EVERYTHING BELOW. The registry and the shape
    // record both used to key on the entry STRINGS. The duplicate guard above
    // keys on the PATH, because that is what the filesystem keys on -- so the
    // same argument was read three different ways in one function, and the two
    // string readings answer a question about spelling while claiming to answer
    // one about the tree.
    //
    // The visible cost is a FALSE alarm rather than a missed one: re-spell an
    // entry -- `Dir//One.olean` for `Dir/One.olean` -- and the registry reports
    // one fixture built twice with different contents, and the record reports a
    // shape change, for a build that produces exactly the same files. Collapsing
    // to the canonical form first makes both answer about the tree. Every
    // existing fixture entry is already canonical, so no recorded shape moves.
    let canonical = |entry: &str| Path::new(entry).components().collect::<PathBuf>();
    let mut requested = relative_files
        .iter()
        .map(|entry| canonical(entry).to_string_lossy().into_owned())
        .collect::<Vec<_>>();
    requested.sort();
    // THE DECISION IS TAKEN UNDER THE LOCK; THE PANIC HAPPENS OUTSIDE IT.
    // Panicking while the guard is alive poisons the Mutex, and every later
    // call from every other test in the process would then fail on the poison
    // rather than on its own merits -- turning one collision into a cascade
    // across unrelated tests, non-deterministically, because these run in
    // parallel. The lock is also taken with the poison ignored, so a panic
    // anywhere else can never disable this registry either.
    let collision = {
        let mut claimed = CLAIMED
            .get_or_init(|| Mutex::new(BTreeMap::new()))
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        match claimed.get(versioned_name) {
            Some(previous) if *previous != requested => Some(previous.clone()),
            _ => {
                claimed.insert(versioned_name.to_string(), requested.clone());
                None
            }
        }
    };
    if let Some(previous) = collision {
        panic!(
            "fixture `{versioned_name}` is built twice with different contents: {previous:?} \
             and {requested:?}. Nothing deletes these trees, so the second build unions into \
             the first and every count taken from either is wrong. Give one of them its own \
             versioned name"
        );
    }

    let base = Path::new(env!("CARGO_TARGET_TMPDIR")).join(versioned_name);
    // AN EMPTY LIBRARY IS A TREE WITH NO FILES, NOT A MISSING TREE. Every
    // directory here used to be created as the PARENT of some entry, so a
    // fixture asked for no entries created nothing and handed back a path to a
    // directory that does not exist. The caller's walk then failed with `read
    // corpus directory ...: No such file or directory` -- which reads as a
    // provisioning fault, not as a library that happens to hold no modules, and
    // sends whoever hits it looking for the fixture writer's bug.
    //
    // That is the same distinction the corpus classifier draws between an absent
    // root and a misprovisioned one, and the same one the retained-receipt
    // reader draws between a file that is not there and a file it cannot read.
    // Third place in this file, and the only one where the two were conflated.
    // THE SHAPE THIS NAME WAS LAST BUILT WITH, RECORDED WHERE THE NEXT RUN CAN
    // SEE IT. Nothing sweeps these trees, so a fixture whose entry list changes
    // without its version being bumped UNIONS into the leftovers of the previous
    // shape: the walk then sees files the current list never mentions, and the
    // count comes out wrong in whichever test is unlucky. The rule until now was
    // a comment asking whoever edits a fixture to remember. This makes it
    // mechanical, and the message names both shapes because "stale fixture" on
    // its own leaves the reader to work out which entry appeared or vanished.
    //
    // BESIDE THE TREE, NOT INSIDE IT. A marker file within `base` would join
    // every walk of that tree, and one test asserts its fixture directory holds
    // no entries AT ALL. A sibling path is invisible to `read_dir(base)` and to
    // every fixture assertion in this file.
    //
    // Written through a temporary and renamed, which is atomic on POSIX. Two
    // tests may legitimately build the same fixture at the same time -- same
    // name, same contents, allowed by the registry above -- and a plain
    // truncating write would let one of them read the other's half-written
    // manifest and report a shape change that never happened.
    let manifest =
        Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("{versioned_name}.manifest"));
    let recorded = requested.join("\n");

    // ABSENT IS NOT THE SAME AS UNREADABLE, AND THIS READ USED TO SAY IT WAS. It
    // was `if let Ok(previous) = ...`, so EVERY error meant "no record": a
    // record that exists but cannot be decoded disabled the guard entirely, the
    // build proceeded on whatever list it was handed, and the write below then
    // replaced the only evidence that anything had been wrong. Silent, and
    // self-erasing.
    //
    // Absent is the one outcome that earns the quiet arm, because a first build
    // is the ordinary case and nobody can fix it from the repository. Anything
    // else is a fault about a file that is there, and it now says so, naming the
    // file. This is the same line the retained-receipt reader draws, and I made
    // that argument at length three commits before writing this one the other
    // way.
    match fs::read_to_string(&manifest) {
        Ok(previous) if previous != recorded => panic!(
            "fixture `{versioned_name}` was built by an earlier run as {:?} and is now asked for \
             as {:?}. Nothing removes these trees, so this build would UNION into that one and \
             every count taken from the result would be over by whatever the old shape left \
             behind. Bump the version in the fixture's name",
            // An empty record means a fixture built with NO entries -- three in
            // this file do. Split naively it renders as `[""]`, which reads as
            // one entry named nothing rather than as none.
            if previous.is_empty() {
                Vec::new()
            } else {
                previous.split('\n').collect::<Vec<_>>()
            },
            requested
        ),
        Ok(_) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => panic!(
            "fixture `{versioned_name}` has a shape record at {} that exists but could not be \
             read: {error}. That is not the same as never having been built -- treating it as \
             absent would build this list over whatever tree the record describes and then \
             overwrite the record, destroying the only evidence of the mismatch",
            manifest.display()
        ),
    }

    // RECORDED BEFORE ANYTHING IS BUILT, AND IT USED TO BE RECORDED AFTER. A
    // build that dies partway -- the disk filling mid-run, which happened twice
    // while this file was being written -- left a PARTIAL tree and no record at
    // all. The next run then saw no shape to compare against, built whatever its
    // list said, and unioned into the leftovers: exactly the hazard this record
    // exists to stop, surviving in the one window where it matters most.
    //
    // Written first, the record always describes the shape that was ATTEMPTED. A
    // retry with the same list matches and completes the tree; a retry with a
    // different list is refused. Both are what the reader wants; neither was
    // true before.
    //
    // AND IT IS A RECORD OF THE REQUEST, NOT OF THE TREE. Five fixtures in this
    // file add files after the writer returns -- two symlinks, a non-UTF-8 name,
    // and two over-cap sparse files -- and the record has never heard of any of
    // them. That is deliberate: the record answers "was this name last built
    // from this list", which is the question the union hazard turns on. Anyone
    // tempted to strengthen it into a hash of the tree would break those five,
    // and `the_shape_record_is_of_the_request_not_of_the_tree` is where the
    // boundary is pinned.
    static MANIFEST_SEQ: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let seq = MANIFEST_SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let staging = manifest.with_extension(format!("manifest-{}-{seq}", std::process::id()));
    fs::write(&staging, recorded.as_bytes())
        .unwrap_or_else(|error| panic!("write {}: {error}", staging.display()));
    fs::rename(&staging, &manifest)
        .unwrap_or_else(|error| panic!("record fixture shape {}: {error}", manifest.display()));

    fs::create_dir_all(&base)
        .unwrap_or_else(|error| panic!("create fixture tree {}: {error}", base.display()));
    for relative in relative_files {
        // Written through the same canonical form the record holds, so the file
        // that lands is the file that was recorded.
        let path = base.join(canonical(relative));
        let parent = path
            .parent()
            .unwrap_or_else(|| panic!("fixture entry {relative} has no parent directory"));
        fs::create_dir_all(parent)
            .unwrap_or_else(|error| panic!("create fixture dir {}: {error}", parent.display()));
        write_entry(&path)
            .unwrap_or_else(|error| panic!("create fixture file {}: {error}", path.display()));
    }
    base
}

/// The fixture-name collision guard actually fires.
///
/// **Why this test exists at all.** Every one of the thirteen fixture names in
/// this file is currently unique, so the guard added beside them never runs. A
/// guard whose condition is satisfied by the whole live population is
/// indistinguishable from one that no longer works -- the shape this bead has
/// found in the empty carve-out registry and in two walk branches. The
/// difference is that this one CAN be shown to fire, so it is, on a name no real
/// fixture uses.
///
/// **The panic is caught rather than expected.** `#[should_panic]` would consume
/// the whole test, and the point is to inspect the MESSAGE: it must name both
/// file sets, because a collision that reports only "duplicate name" leaves the
/// reader to work out which two tests are fighting over the tree. The panic hook
/// is silenced around the call so a deliberate panic does not look like a
/// failure in the log, and restored immediately after.
///
/// **A second pair exists because the first cannot distinguish the rule from a
/// cheaper one.** Both of its lists hold a single entry and those entries are
/// disjoint, so comparing only the first element of each sorted list refuses
/// them just as a whole-list comparison does. The pair at the end shares
/// `Alpha.olean` and differs after it: only comparing the whole list refuses it,
/// and the agreement about the first entry is asserted so the cell cannot drift
/// into a copy of the one above.
#[test]
fn the_fixture_collision_guard_names_both_contents() {
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let claimed_twice = std::panic::catch_unwind(|| {
        write_inventory_fixture("t6r7-selftest-collision-v1", &["first.olean"]);
        // Same name, different contents: the second build would union into the
        // first if nothing stopped it.
        write_inventory_fixture("t6r7-selftest-collision-v1", &["second.olean"]);
    });
    std::panic::set_hook(previous);

    let payload =
        claimed_twice.expect_err("a fixture name reused with different contents must be refused");
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap_or_default();
    assert!(
        message.contains("first.olean") && message.contains("second.olean"),
        "the refusal must name BOTH file sets, or the reader cannot tell which two fixtures \
         collided: {message}"
    );
    assert!(
        message.contains("t6r7-selftest-collision-v1"),
        "the refusal must name the fixture: {message}"
    );

    // AND THE SAME NAME WITH THE SAME CONTENTS IS FINE -- a test may rebuild its
    // own fixture. Without this the guard could be refusing every second call
    // rather than every colliding one, and the check above could not tell.
    write_inventory_fixture("t6r7-selftest-collision-v1", &["first.olean"]);

    // A COLLISION THAT AGREES ABOUT ITS FIRST ENTRY. Both lists above hold ONE
    // entry and those entries are disjoint, so a rule comparing only the first
    // element of each sorted list refuses them exactly as the real one does, and
    // nothing here tells the two apart. The pair below shares `Alpha.olean` and
    // differs after it, which only a comparison of the whole list refuses.
    // Measured against both rules, with the two green cases, before this cell
    // was written.
    const SHARED_FIRST: &str = "t6r7-selftest-collision-tail-v1";
    write_inventory_fixture(SHARED_FIRST, &["Alpha.olean", "One.olean"]);

    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let tail_differs = std::panic::catch_unwind(|| {
        write_inventory_fixture(SHARED_FIRST, &["Alpha.olean", "Two.olean"])
    });
    std::panic::set_hook(previous);

    let payload = tail_differs.err().unwrap_or_else(|| {
        panic!("two lists agreeing only about their first entry are still different contents")
    });
    let tail_message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap_or_default();
    assert!(
        tail_message.contains("One.olean") && tail_message.contains("Two.olean"),
        "the refusal must name the entries that actually differ, which are not the first ones: \
         {tail_message}"
    );

    // THE SHARED ENTRY IS ASSERTED TO BE THE FIRST ONE, in code and after
    // sorting, because that is the whole property. If the lists were ever edited
    // so they differed at position zero, the cheap rule would refuse them too and
    // this cell would silently become a second copy of the one above.
    let mut left = ["Alpha.olean", "One.olean"];
    let mut right = ["Alpha.olean", "Two.olean"];
    left.sort_unstable();
    right.sort_unstable();
    assert_eq!(
        left.first(),
        right.first(),
        "the two lists must AGREE about their first entry after sorting, or they do not \
         distinguish a whole-list comparison from a first-entry one"
    );
    assert_ne!(
        left, right,
        "and they must still differ somewhere, or there is no collision to refuse"
    );
}

/// The walk branch, driven by a fixture instead of by a corpus nobody has.
///
/// **Why this exists.** Every property of the walk was, until now, reachable
/// only on a host with `/data/tmp/mathlib4-corpus`, and no host has it. The walk
/// test therefore always took its skip arm, so the enumeration, the extension
/// filter, the namespace qualification and the injectivity check were written
/// but never executed -- and code that never executes is indistinguishable from
/// code that is wrong. Three empty files make the success path reachable.
///
/// **What it deliberately does NOT do.** It does not touch, create, or stand in
/// for the Mathlib corpus, and passing it is not evidence about Mathlib. It says
/// the walk's tree-shape logic behaves on a tree whose right answer is known by
/// construction.
#[test]
fn the_inventory_walk_runs_on_a_fixture_tree_without_a_corpus() {
    let library = write_inventory_fixture(
        "t6r7-inventory-ok-v1",
        &[
            "Alpha.olean",
            "Nested/Beta.olean",
            "Nested/Gamma.olean",
            // Neither of these is an olean, and both are shaped to catch a
            // filter written as "contains" rather than "extension is": a
            // companion part and an ordinary file.
            "Alpha.olean.server",
            "ignored.txt",
        ],
    );

    // THE DECOYS MUST BE THERE, or the filter has nothing to reject. Removing
    // them from the list above leaves every assertion in this test passing --
    // three oleans is still three -- while the property the fixture exists to
    // exercise quietly stops being exercised. The strength lives in the INPUT,
    // so the input is asserted.
    for decoy in ["Alpha.olean.server", "ignored.txt"] {
        assert!(
            library.join(decoy).is_file(),
            "the decoy `{decoy}` is missing from the fixture, so nothing here tests that a \
             companion part and a text file are skipped"
        );
    }

    let OleanInventory { oleans, modules } = walk_olean_inventory(&library, Some("Fixture"))
        .unwrap_or_else(|reason| panic!("the fixture tree must be walkable: {reason}"));

    assert_eq!(
        oleans.len(),
        3,
        "the walk must enumerate exactly the three `.olean` files; a companion part and a text \
         file are not oleans. Found: {oleans:?}"
    );
    assert_eq!(
        modules,
        vec![
            "Fixture.Alpha".to_string(),
            "Fixture.Nested.Beta".to_string(),
            "Fixture.Nested.Gamma".to_string(),
        ],
        "the walk must recurse into subdirectories, drop the extension, join components with \
         `.`, qualify with the namespace, and return the result in canonical path order"
    );
}

/// The injectivity check is not decorative: a tree that violates it is REFUSED.
///
/// **The collision is real, not contrived.** `module_name_from_path` strips the
/// root, drops the final extension and joins the remaining components with `.`,
/// so `A/B.olean` and `A.B.olean` both project to `A.B`. Two distinct files, one
/// module name. Without the check the inventory would report one module where
/// two files exist, under-counting by exactly as much as it collided -- and an
/// under-count is invisible, because a smaller number looks like a smaller
/// corpus rather than like a bug.
///
/// This is the negative half of the control above. A guard that has only ever
/// been shown to accept good input has not been shown to do anything.
#[test]
fn the_inventory_walk_refuses_a_non_injective_projection() {
    let library =
        write_inventory_fixture("t6r7-inventory-collision-v1", &["A/B.olean", "A.B.olean"]);

    let reason = match walk_olean_inventory(&library, Some("Fixture")) {
        Err(reason) => reason,
        Ok(OleanInventory { oleans, modules }) => panic!(
            "the walk ACCEPTED a tree whose projection collides: {} olean(s) became {:?}. Two \
             files sharing one module name means the inventory under-counts, and nothing \
             downstream can tell that from a smaller corpus.",
            oleans.len(),
            modules
        ),
    };
    assert!(
        reason.contains("not injective"),
        "the refusal must name the non-injectivity rather than some incidental mismatch: \
         {reason}"
    );

    // AND IT MUST NAME THE COLLISION. Counting it is what the message used to
    // do, and two numbers are exactly as useful on a two-file fixture as they
    // are useless on the corpus -- which is the only tree where this guard fires
    // without someone having built the collision on purpose.
    assert!(
        reason.contains("Fixture.A.B"),
        "the refusal must name the module name the two files collided ON, or the reader has to \
         re-run the projection to find out which one it was: {reason}"
    );
    // BOTH paths, asserted separately. A message naming only the first file
    // satisfies half of this and leaves the whole search behind -- the half that
    // costs, since the point of the pair is that they are different files.
    assert!(
        reason.contains("A/B.olean"),
        "the refusal must name the nested file: {reason}"
    );
    assert!(
        reason.contains("A.B.olean"),
        "the refusal must name the dotted file: {reason}"
    );
}

/// Two files with one name, separated in the emitted order by a third.
///
/// **Both existing collision fixtures put the repeat next to itself.**
/// `A/B.olean` beside `A.B.olean` emits `["A.B", "A.B"]`, and the four-pair
/// fixture emits each pair adjacent too. So a rule written as an adjacent
/// dedupe -- `windows(2).any(|w| w[0] == w[1])`, the cheap way to spot a repeat
/// in a list somebody assumes is sorted -- refuses both and cannot be told apart
/// from the real one.
///
/// **The list is in PATH order, not name order, which is what makes the gap
/// reachable.** That was established when the parent-module ordering was pinned:
/// `modules[i]` is the projection of `oleans[i]`, and paths sort by component.
/// So a third file whose PATH falls between two colliding ones separates their
/// equal names. `A/C.olean` does exactly that -- `A/B.olean` < `A/C.olean` <
/// `A.B.olean` -- and the emitted names come out `["A.B", "A.C", "A.B"]`.
///
/// **The separation is asserted from the real projection, not assumed.** The
/// names are read back through `module_names_below`, which projects without
/// checking injectivity, so the cell can state where the two occurrences landed.
/// If a future change sorted the names, they would become adjacent again and
/// this assertion -- not the refusal -- is what would say so.
#[test]
fn a_collision_split_by_a_third_file_is_still_refused() {
    let library = write_inventory_fixture(
        "t6r7-inventory-split-collision-v1",
        &["A/B.olean", "A/C.olean", "A.B.olean"],
    );

    // WHERE THE EQUAL NAMES ACTUALLY LAND. `module_names_below` projects in path
    // order and does not check injectivity, so it can show the emitted sequence
    // that the walk is about to refuse.
    let ordered = module_names_below(&library, Some("Fixture"))
        .unwrap_or_else(|reason| panic!("the projection itself must succeed: {reason}"));
    assert_eq!(
        ordered.len(),
        3,
        "all three files must project before their order means anything: {ordered:?}"
    );
    let first = ordered
        .iter()
        .position(|name| name == "Fixture.A.B")
        .unwrap_or_else(|| panic!("the colliding name is missing: {ordered:?}"));
    let second = ordered
        .iter()
        .rposition(|name| name == "Fixture.A.B")
        .unwrap_or_else(|| panic!("the colliding name appears once: {ordered:?}"));
    assert!(
        second > first + 1,
        "the two occurrences of `Fixture.A.B` must be SEPARATED, or an adjacent dedupe would \
         catch them and this fixture adds nothing to the two that already exist: {ordered:?}"
    );

    let reason = match walk_olean_inventory(&library, Some("Fixture")) {
        Err(reason) => reason,
        Ok(accepted) => panic!(
            "two files sharing one module name were accepted because a third sorted between \
             them: {:?}",
            accepted.modules
        ),
    };
    assert!(
        reason.contains("not injective"),
        "the refusal must be the injectivity rule's: {reason}"
    );
    assert!(
        reason.contains("Fixture.A.B"),
        "the refusal must name the module the two files collided on: {reason}"
    );
    // The file that merely sits between them is not part of the collision and
    // must not be reported as though it were.
    assert!(
        !reason.contains("Fixture.A.C"),
        "`Fixture.A.C` collides with nothing; naming it would send the reader to a third file \
         that is doing no harm: {reason}"
    );
}

/// Many collisions are summarised, and the message says how many it dropped.
///
/// **A cap that says nothing about what it hid reads as a complete list.** The
/// refusal shows the first few colliding names and stops; if it stopped
/// silently, an operator reading three collisions off a corpus-scale tree would
/// fix three and re-run, and the walk would refuse again for a reason the
/// message had already declined to mention. So the remainder is counted out
/// loud, and this test is what makes that sentence true rather than intended.
///
/// **Four collisions against a cap of three**, which is the smallest fixture
/// that can tell "shows everything" from "shows some and admits it". The dropped
/// name is asserted ABSENT as well as counted -- without that, a message that
/// listed all four while also claiming one was omitted would pass.
#[test]
fn many_collisions_are_summarised_without_hiding_how_many() {
    let library = write_inventory_fixture(
        "t6r7-inventory-many-collisions-v1",
        &[
            "A/Y.olean",
            "A.Y.olean",
            "B/Y.olean",
            "B.Y.olean",
            "C/Y.olean",
            "C.Y.olean",
            "D/Y.olean",
            "D.Y.olean",
        ],
    );

    let reason = match walk_olean_inventory(&library, Some("Fixture")) {
        Err(reason) => reason,
        Ok(accepted) => panic!(
            "eight files projecting to four names were accepted as {:?}",
            accepted.modules
        ),
    };

    assert!(
        reason.contains("4 name(s) collide"),
        "the refusal must count ALL the collisions, not the ones it chose to print: {reason}"
    );
    for shown in ["Fixture.A.Y", "Fixture.B.Y", "Fixture.C.Y"] {
        assert!(
            reason.contains(shown),
            "`{shown}` is within the cap and must be listed: {reason}"
        );
    }
    assert!(
        reason.contains("1 more colliding name(s) not listed"),
        "the message must say what it dropped; a cap nobody is told about is indistinguishable \
         from a complete list: {reason}"
    );
    // THE DROPPED ONE IS REALLY DROPPED. `D.Y.olean` covers the paths and
    // `Fixture.D.Y` the name, so neither half of the fourth group can be
    // present while the message claims it was omitted.
    assert!(
        !reason.contains("Fixture.D.Y") && !reason.contains("D.Y.olean"),
        "the fourth collision is claimed to be omitted and appears anyway, so the count and the \
         list disagree about the same message: {reason}"
    );
}

/// `collect_present_oleans` is canonical BEFORE any caller sorts it.
///
/// **Three sorts, and not one of them could be killed.** The walk's order is
/// established three times over: once inside the helper, once in
/// `module_names_below`, once in `walk_olean_inventory`. Every existing
/// assertion reads the walk's output, which is re-sorted on the way out, so
/// deleting any single sort leaves every test green -- and the neighbouring
/// test's doc claimed the opposite until this commit. A declaration that no
/// mutant can falsify is indistinguishable from one that no longer works.
///
/// **This caller is the one that does not re-sort.** It reads the helper
/// directly, so the innermost sort is the only thing standing between it and
/// whatever order the filesystem hands back. That makes exactly one of the three
/// observable; the other two are declared inert where they sit rather than left
/// looking like escaped mutants.
///
/// **What the helper's order is worth.** A depth-first walk with entries sorted
/// by file name within each directory emits paths in the global path order --
/// component-wise comparison IS lexicographic order on the component sequence --
/// so a direct caller can rely on the result being canonical without sorting it
/// again. That is a contract worth pinning independently of the walk, because
/// the walk is not its only caller: the empty-segment test reads it to show a
/// file reaches the projection, and a future one will read it for its order.
///
/// **The observation depends on the filesystem, and that is disclosed rather
/// than assumed.** If `read_dir` happened to return entries already sorted, an
/// unsorted helper would pass this test. The raw order is read first and
/// compared; when it cannot distinguish the two implementations the test says so
/// in a typed line instead of reporting a green that means nothing. On the host
/// this was written for, `read_dir` returns neither sorted nor creation order.
#[test]
fn the_walk_helper_is_canonical_before_any_caller_sorts_it() {
    const CREATED: [&str; 6] = [
        "Zeta.olean",
        "Mid.olean",
        "Alpha.olean",
        "Nested/Zulu.olean",
        "Nested/Alfa.olean",
        "Algebra/Basic.olean",
    ];
    let library = write_inventory_fixture("t6r7-inventory-helper-order-v1", &CREATED);

    // ANTI-VACUITY ON THE FIXTURE: created out of sorted order, or an unsorted
    // helper could return creation order and satisfy everything below.
    let mut expected_order = CREATED.to_vec();
    expected_order.sort_unstable();
    assert_ne!(
        CREATED.to_vec(),
        expected_order,
        "the fixture must be created OUT of sorted order: {CREATED:?}"
    );

    // WHAT THE FILESYSTEM ACTUALLY HANDS BACK. Read before the helper, so the
    // disclosure below is about this tree rather than about a hoped-for one.
    let raw = fs::read_dir(&library)
        .unwrap_or_else(|error| panic!("read {}: {error}", library.display()))
        .map(|entry| {
            entry
                .unwrap_or_else(|error| panic!("enumerate {}: {error}", library.display()))
                .file_name()
        })
        .collect::<Vec<_>>();
    let mut raw_sorted = raw.clone();
    raw_sorted.sort();
    if raw == raw_sorted {
        println!(
            "{{\"schema\":\"fln-t6r7-helper-order/1\",\"status\":\"observation_cannot_distinguish\",\
             \"claims\":\"NOTHING about the helper's sort. This filesystem returned directory \
             entries already in sorted order, so an unsorted helper would satisfy the assertions \
             below as well as a sorted one.\"}}"
        );
    }

    let mut collected = Vec::new();
    collect_present_oleans(&library, &mut collected)
        .unwrap_or_else(|reason| panic!("the fixture must enumerate: {reason}"));
    assert_eq!(
        collected.len(),
        CREATED.len(),
        "every fixture file must be collected before its order means anything: {collected:?}"
    );

    // THE CONTRACT: the helper's own output, untouched, IS the canonical order.
    // Stated as an equality against a sorted copy rather than as `windows(2)`,
    // because a helper that returned a sorted SUBSET would satisfy the pairwise
    // form and this one also pins that nothing moved.
    let mut canonical = collected.clone();
    canonical.sort();
    assert_eq!(
        collected, canonical,
        "the helper returned paths in an order no caller established. Every caller in this file \
         re-sorts, so this is the only place the helper's own guarantee is visible -- and a \
         direct caller that trusted it would silently get filesystem order"
    );
    assert!(
        collected[0].ends_with("Algebra/Basic.olean"),
        "`Algebra/Basic.olean` sorts first and `Zeta.olean` was created first; the helper is \
         reporting an order it did not choose: {collected:?}"
    );
}

/// The 512 MB corpus cap is refused from `stat`, and it had never fired.
///
/// **A cap nobody has ever seen refuse anything.** `MAX_PINNED_OLEAN_BYTES` is
/// read at two sites and, before this test, the only occurrences of the words
/// `corpus cap` anywhere in `crates/` were the two message literals themselves.
/// Nothing had ever produced either refusal, so the arithmetic, the comparison
/// direction and the wording were all unobserved -- the same shape as the empty
/// carve-out registry and the three unkillable sorts, and the reason a limit
/// that has never fired is indistinguishable from one that cannot.
///
/// **Planting it costs nothing, which is why there was no excuse.** The per-part
/// check reads `metadata.len()` -- the APPARENT size -- so `File::set_len` makes
/// a half-gigabyte file that occupies no blocks at all. No corpus, no half a
/// gigabyte of disk, no half a gigabyte of memory: the refusal happens before
/// `fs::read` is reached, so nothing ever materialises those bytes. The
/// sparseness is asserted rather than assumed on unix, because "this fixture is
/// free" is the claim that decides whether it is safe to leave behind in a tree
/// that nothing sweeps.
///
/// **What this does NOT show, said plainly so nobody reads it as more.**
///
/// It does not show the check runs BEFORE the read. Both caps use the same
/// constant, so the per-part check refuses nothing the aggregate would not also
/// refuse; its whole value is that it refuses without allocating, and a version
/// that checked after `fs::read` would return the same `Err` and pass every
/// assertion here. Distinguishing them needs an observation of allocation or of
/// a file whose read fails while its stat succeeds, and neither is portable.
///
/// It does not pin the comparison DIRECTION. The test file is one byte over, so
/// `>` and `>=` both refuse it. A cell for exactly `MAX_PINNED_OLEAN_BYTES` would
/// separate them, and it would have to read half a gigabyte of zeros into a
/// `Vec` in a test binary that runs its tests in parallel. That is the price, and
/// it is why the boundary is disclosed rather than tested.
///
/// It does not touch the AGGREGATE cap at the second site. That one sums three
/// decoded parts, so firing it needs a module whose public, server and private
/// parts all parse -- a corpus artifact, not a fixture tree. It stays unobserved,
/// and what would produce it is a decodable three-part module fixture, not more
/// argument.
#[test]
fn an_over_cap_module_part_is_refused_and_the_refusal_names_both_numbers() {
    let library = write_inventory_fixture("t6r7-sparse-over-cap-v1", &[]);
    let over_cap = library.join("Huge.olean");

    // SPARSE, NOT WRITTEN. `set_len` sets the size and allocates nothing; the
    // file is created or re-truncated on every run and never removed, like every
    // other fixture here.
    let handle = fs::File::create(&over_cap)
        .unwrap_or_else(|error| panic!("create {}: {error}", over_cap.display()));
    handle
        .set_len(MAX_PINNED_OLEAN_BYTES + 1)
        .unwrap_or_else(|error| panic!("size {}: {error}", over_cap.display()));
    drop(handle);

    // ANTI-VACUITY ON THE FIXTURE, BOTH WAYS. The apparent size must really be
    // one byte over -- a `set_len` that silently did nothing would leave an
    // empty file, which is under the cap and would make the refusal below
    // impossible to explain -- and the file must really be sparse, or this test
    // has quietly started costing half a gigabyte per run.
    let metadata = fs::metadata(&over_cap)
        .unwrap_or_else(|error| panic!("stat {}: {error}", over_cap.display()));
    assert_eq!(
        metadata.len(),
        MAX_PINNED_OLEAN_BYTES + 1,
        "the fixture must be exactly one byte over the cap, or the refusal below is about a \
         different number than this test claims"
    );
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        let allocated = metadata.blocks() * 512;
        assert!(
            allocated < 1024 * 1024,
            "the over-cap fixture allocated {allocated} bytes on disk. It is supposed to be a \
             hole: `set_len` reserves no blocks, and a fixture that nothing sweeps must not leave \
             half a gigabyte behind on every host that runs this suite"
        );
    }

    // Matched rather than `expect_err`: the `Ok` arm holds the file's CONTENTS,
    // and formatting it would print half a gigabyte of zeros into the failure
    // log at the exact moment the cap stopped working.
    let reason = match read_corpus_module_part(&over_cap) {
        Err(reason) => reason,
        Ok(bytes) => panic!(
            "a part {} bytes over the {MAX_PINNED_OLEAN_BYTES}-byte cap was read anyway, {} \
             bytes of it",
            metadata.len() - MAX_PINNED_OLEAN_BYTES,
            bytes.len()
        ),
    };

    // BOTH NUMBERS, SEPARATELY. A refusal naming only the cap leaves the reader
    // to stat the file, and one naming only the size leaves them to find the cap
    // in the source; the whole point of the message is that neither trip is
    // necessary.
    assert!(
        reason.contains(&metadata.len().to_string()),
        "the refusal must name the size the file actually is: {reason}"
    );
    assert!(
        reason.contains(&MAX_PINNED_OLEAN_BYTES.to_string()),
        "the refusal must name the cap it exceeded: {reason}"
    );
    assert!(
        reason.contains("Huge.olean"),
        "the refusal must name the file, or on a corpus-scale sweep it says only that SOMETHING \
         was too big: {reason}"
    );

    // GREEN CONTROL. An ordinary part must still be read, and its bytes returned
    // unchanged -- without this the cap could be refusing everything and every
    // assertion above would still hold.
    let ordinary = library.join("Small.olean");
    fs::write(&ordinary, b"not-really-an-olean")
        .unwrap_or_else(|error| panic!("write {}: {error}", ordinary.display()));
    assert_eq!(
        read_corpus_module_part(&ordinary)
            .unwrap_or_else(|reason| panic!("a small part must be read: {reason}")),
        b"not-really-an-olean",
        "the reader must return the file's bytes; the cap is a limit, not a filter"
    );
}

/// The cap refuses WITHOUT reaching the read.
///
/// **The hole this closes was disclosed one commit ago and is the whole point of
/// the cap.** `an_over_cap_module_part_is_refused_and_the_refusal_names_both_numbers`
/// shows the refusal happens and shows what it says. It cannot show WHEN: a
/// version that read the file first and checked the size afterwards returns the
/// same `Err`, with the same words, about the same file -- after pulling half a
/// gigabyte into memory. Since both cap sites share one constant, the per-part
/// check changes no verdict at all; refusing before allocating is the only thing
/// it is for, and that was exactly the part nothing tested.
///
/// **Observed by making the read a parameter, not by observing an allocation.**
/// The reader passed here panics if it is ever called. If the check runs first
/// the refusal comes back and the closure never runs; if it moved after the
/// read, the closure fires and this test fails naming the reason. No allocation
/// counter, no timing, no platform assumption -- the same parametric-probe move
/// this repository already uses when the fact to establish is an exact
/// operation rather than a value.
///
/// **The injection is green-controlled, or the first cell is vacuous.** A
/// `read_corpus_module_part_with` that never called its reader under ANY
/// condition would satisfy the panic cell perfectly. So an under-cap file is
/// read through an injected reader returning a sentinel, and that sentinel must
/// come back: the reader is reached when the cap does not refuse, and its result
/// is what the function returns.
///
/// **What stays unpinned, so it is not read as more.** The ordering is pinned
/// INSIDE `read_corpus_module_part_with`. Production is a one-line delegation to
/// it, visible in the same screenful, and a future version that read the file
/// before delegating would not be caught here. Binding that too would need the
/// production wrapper to be the thing under test, which is what a parametric
/// probe trades away.
#[test]
fn the_cap_refuses_without_reaching_the_read() {
    // A FIXTURE NAME OF ITS OWN, not the one the neighbouring cap test uses.
    // Sharing it would have two tests `File::create` the same over-cap file, and
    // `create` truncates: in a parallel run one test's `set_len` lands between
    // the other's truncate and its `stat`, and the size assertion fails for a
    // reason that has nothing to do with the cap.
    let library = write_inventory_fixture("t6r7-sparse-cap-order-v1", &[]);
    let over_cap = library.join("Huge.olean");
    let handle = fs::File::create(&over_cap)
        .unwrap_or_else(|error| panic!("create {}: {error}", over_cap.display()));
    handle
        .set_len(MAX_PINNED_OLEAN_BYTES + 1)
        .unwrap_or_else(|error| panic!("size {}: {error}", over_cap.display()));
    drop(handle);

    let metadata = fs::metadata(&over_cap)
        .unwrap_or_else(|error| panic!("stat {}: {error}", over_cap.display()));
    assert_eq!(
        metadata.len(),
        MAX_PINNED_OLEAN_BYTES + 1,
        "the fixture must be over the cap, or the reader below is skipped for the ordinary reason \
         that the file is small"
    );
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        let allocated = metadata.blocks() * 512;
        assert!(
            allocated < 1024 * 1024,
            "the over-cap fixture allocated {allocated} bytes on disk; it is supposed to be a hole"
        );
    }

    // THE READER MUST NOT RUN. If the cap moved after the read this panics, and
    // the message says which of the two orders was observed rather than leaving
    // a bare unwind in the log.
    let reason = match read_corpus_module_part_with(&over_cap, || {
        panic!(
            "the reader ran for a file the cap had already seen was too big. The size check has \
             moved AFTER the read, so the refusal now costs the half gigabyte it exists to avoid \
             -- and every assertion about the returned error still passes"
        )
    }) {
        Err(reason) => reason,
        Ok(bytes) => panic!(
            "an over-cap part was accepted, {} bytes of it, without the reader being reached",
            bytes.len()
        ),
    };
    assert!(
        reason.contains("corpus cap"),
        "the refusal must be the cap's, not some other failure that also skipped the read: \
         {reason}"
    );

    // GREEN CONTROL ON THE INJECTION. Without this, a function that never called
    // its reader would pass the cell above for the wrong reason.
    let under_cap = library.join("Small.olean");
    fs::write(&under_cap, b"on-disk-bytes")
        .unwrap_or_else(|error| panic!("write {}: {error}", under_cap.display()));
    let sentinel = b"bytes-from-the-injected-reader".to_vec();
    let returned = read_corpus_module_part_with(&under_cap, || Ok(sentinel.clone()))
        .unwrap_or_else(|reason| panic!("an under-cap part must be read: {reason}"));
    assert_eq!(
        returned, sentinel,
        "the injected reader must be REACHED when the cap does not refuse, and what it returns \
         must be what the function returns -- otherwise the panic cell above is satisfied by a \
         reader that is never called at all"
    );

    // AND PRODUCTION IS WIRED TO THE FILESYSTEM. The probe proves an order; this
    // proves the order is about reading this file, not about a reader that only
    // exists in a test.
    assert_eq!(
        read_corpus_module_part(&under_cap)
            .unwrap_or_else(|reason| panic!("the production reader must read: {reason}")),
        b"on-disk-bytes",
        "the one-line wrapper must pass `fs::read`, or the ordering pinned above is about \
         something production does not do"
    );
}

/// A fixture rebuilt with a DIFFERENT shape is refused, across runs.
///
/// **The hazard was a comment asking people to remember.** The name registry
/// catches two tests claiming one fixture name inside one process. The other
/// half -- an earlier RUN having built this name with a different entry list --
/// outlives the process that could have noticed, and the writer's own comment
/// said so: the cross-run case "stays with the versioned name and its comment".
/// Nothing removes these trees, so the next build unions into the leftovers, the
/// walk sees files the current list never mentions, and the count comes out
/// wrong in whichever test the interleaving disadvantages.
///
/// **Demonstrated on a planted member, because the live population is empty.**
/// Every fixture name in this file is built with one shape, so the guard would
/// never run and a guard whose condition nothing satisfies is indistinguishable
/// from one that no longer works. The stale manifest here is written by hand for
/// a name no real fixture uses -- the same move the collision self-test makes,
/// and the only way to see a cross-run failure inside one run.
///
/// **The refusal names both shapes.** "Stale fixture" leaves the reader to work
/// out which entry appeared or vanished, which is the entire question when a
/// count is off by one.
///
/// **Two planted records, because one of them cannot distinguish the rule from
/// its cheap version.** The first holds two entries against a one-entry build,
/// so "did the number of entries change" refuses it as well. The second is one
/// entry on each side with different names -- a shape change that does not
/// change the size -- and only a content comparison refuses it. Its tree is
/// planted too, so the harm is exhibited: the refused build must not have added
/// its entry to the stale tree.
///
/// **The record sits BESIDE the tree, not inside it**, and that is asserted:
/// a marker file within the fixture directory would join every walk of it, and
/// `an_empty_library_walks_to_nothing_and_a_missing_one_does_not_walk` requires
/// its tree to hold no entries at all.
#[test]
fn a_fixture_rebuilt_with_a_different_shape_is_refused() {
    let tmp = Path::new(env!("CARGO_TARGET_TMPDIR"));

    // GREEN CONTROL FIRST, and it is what makes the refusal below meaningful: an
    // ordinary build must record its shape, and building the same name with the
    // same contents again must still be allowed.
    let ok = write_inventory_fixture("t6r7-selftest-manifest-ok-v1", &["Kept.olean"]);
    let ok_manifest = tmp.join("t6r7-selftest-manifest-ok-v1.manifest");
    let recorded = fs::read_to_string(&ok_manifest)
        .unwrap_or_else(|error| panic!("read {}: {error}", ok_manifest.display()));
    assert_eq!(
        recorded, "Kept.olean",
        "the writer must record the shape it built, or the refusal below is guarding on nothing"
    );
    assert!(
        !ok_manifest.starts_with(&ok),
        "the record must sit beside the tree at {}, not inside {} where every walk of the fixture \
         would see it",
        ok_manifest.display(),
        ok.display()
    );
    assert_eq!(
        write_inventory_fixture("t6r7-selftest-manifest-ok-v1", &["Kept.olean"]),
        ok,
        "the same name with the same contents must still rebuild; a test may build its own \
         fixture twice"
    );

    // THE PLANTED PREVIOUS RUN. Written by hand, because a real one cannot
    // happen twice inside a single process.
    let stale = tmp.join("t6r7-selftest-manifest-stale-v1.manifest");
    fs::write(&stale, b"Gone.olean\nKept.olean")
        .unwrap_or_else(|error| panic!("write {}: {error}", stale.display()));

    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let rebuilt = std::panic::catch_unwind(|| {
        write_inventory_fixture("t6r7-selftest-manifest-stale-v1", &["Kept.olean"])
    });
    std::panic::set_hook(previous);

    let payload = rebuilt
        .err()
        .unwrap_or_else(|| panic!("a fixture rebuilt with a different shape must be refused"));
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap_or_default();

    // BOTH SHAPES, ASSERTED SEPARATELY. `Gone.olean` is the entry that would
    // have been left behind and is the whole content of the warning; `Kept.olean`
    // is in both shapes and proves the message shows the new list rather than
    // only the difference.
    assert!(
        message.contains("Gone.olean"),
        "the refusal must name what the earlier run left behind: {message}"
    );
    assert!(
        message.contains("Kept.olean"),
        "the refusal must name the shape being asked for now: {message}"
    );
    assert!(
        message.contains("t6r7-selftest-manifest-stale-v1"),
        "the refusal must name the fixture: {message}"
    );

    // AND NOTHING WAS BUILT. The check has to precede the writes, or the stale
    // tree has already been unioned into by the time anyone is told.
    assert!(
        !tmp.join("t6r7-selftest-manifest-stale-v1").exists(),
        "the rebuild was refused and its tree exists anyway; the shape check must run BEFORE the \
         files are written"
    );

    // A SHAPE CHANGE THAT DOES NOT CHANGE THE SIZE. The planted record above
    // holds two entries and the build asks for one, so a cheap rule -- did the
    // number of entries change -- refuses it as well and cannot be told apart
    // from the real one. This pair is one entry on each side with different
    // names, which only a content comparison refuses. Measured against both
    // rules, with the green case, before this cell was written.
    const SAME_SIZE: &str = "t6r7-selftest-manifest-same-size-v1";
    let same_size_record = tmp.join(format!("{SAME_SIZE}.manifest"));
    let same_size_tree = tmp.join(SAME_SIZE);
    fs::write(&same_size_record, b"Gone.olean")
        .unwrap_or_else(|error| panic!("plant the same-size record: {error}"));
    // The tree the record describes, planted too, so the harm is exhibited
    // rather than argued: this is what the new list would union into.
    fs::create_dir_all(&same_size_tree)
        .unwrap_or_else(|error| panic!("plant the stale tree: {error}"));
    fs::write(same_size_tree.join("Gone.olean"), b"")
        .unwrap_or_else(|error| panic!("plant the stale file: {error}"));

    // THE SIZES MUST MATCH, SAID IN CODE. If this record were ever edited to a
    // second entry, the cheap rule would refuse it too and the cell would become
    // another copy of the one above without failing.
    let planted = fs::read_to_string(&same_size_record)
        .unwrap_or_else(|error| panic!("read the same-size record: {error}"));
    assert_eq!(
        planted.lines().count(),
        1,
        "the planted record and the requested list must hold the SAME number of entries, or this \
         cell does not distinguish a content comparison from a size one"
    );

    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let same_size =
        std::panic::catch_unwind(|| write_inventory_fixture(SAME_SIZE, &["Kept.olean"]));
    std::panic::set_hook(previous);
    let payload = same_size.err().unwrap_or_else(|| {
        panic!("one entry replaced by a different one is still a shape change and must be refused")
    });
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap_or_default();
    assert!(
        message.contains("Gone.olean") && message.contains("Kept.olean"),
        "the refusal must name what the earlier run left behind and what is asked for now: \
         {message}"
    );

    // THE HARM, EXHIBITED. The stale tree is untouched: the entry the new list
    // named was never added to it, which is exactly what a union would have done.
    assert!(
        same_size_tree.join("Gone.olean").is_file(),
        "the planted stale file must still be there; nothing here sweeps"
    );
    assert!(
        !same_size_tree.join("Kept.olean").exists(),
        "the refused build added its entry to the stale tree anyway, which is the union this \
         record exists to prevent"
    );

    // A RECORD THAT IS EMPTY IS STILL A RECORD. Both planted records above hold
    // text, so a rule that treated an empty one as "never built" -- an easy
    // reading, since an empty file looks like nothing was written -- refuses
    // both and cannot be told apart from the real one. Three fixtures in this
    // file are built with no entries at all and therefore record exactly that,
    // so the gap is not hypothetical: it would disable the guard for every one
    // of them.
    const WAS_EMPTY: &str = "t6r7-selftest-manifest-was-empty-v1";
    let empty_record = tmp.join(format!("{WAS_EMPTY}.manifest"));
    let empty_tree = tmp.join(WAS_EMPTY);
    fs::write(&empty_record, b"").unwrap_or_else(|error| panic!("plant the empty record: {error}"));
    // The tree that record describes is empty too, but a stale FILE is what a
    // union would carry in, so one is planted to make the harm visible.
    fs::create_dir_all(&empty_tree).unwrap_or_else(|error| panic!("plant the stale tree: {error}"));
    fs::write(empty_tree.join("Left.olean"), b"")
        .unwrap_or_else(|error| panic!("plant the stale file: {error}"));

    // THE DISCRIMINATING PROPERTY, READ BACK FROM DISK. If this record ever held
    // text, the easy rule would refuse it too and the cell would stop
    // distinguishing anything.
    assert!(
        fs::read_to_string(&empty_record)
            .unwrap_or_else(|error| panic!("read the empty record: {error}"))
            .is_empty(),
        "the planted record must be EMPTY, which is the whole property this cell turns on"
    );

    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let from_empty =
        std::panic::catch_unwind(|| write_inventory_fixture(WAS_EMPTY, &["Kept.olean"]));
    std::panic::set_hook(previous);
    let payload = from_empty.err().unwrap_or_else(|| {
        panic!("a fixture recorded as holding no entries is still a recorded shape")
    });
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap_or_default();
    assert!(
        message.contains("Kept.olean") && !message.contains("could not be read"),
        "an empty record must be refused as a SHAPE CHANGE, not as an unreadable file: {message}"
    );
    assert!(
        message.contains("as [] and is now asked for"),
        "a record of no entries must render as `[]`; `[\"\"]` reads as one entry named nothing: \
         {message}"
    );

    assert!(
        !empty_tree.join("Kept.olean").exists(),
        "the refused build added its entry to a tree recorded as empty, which is the union the \
         record exists to prevent"
    );
}

/// A fixture list that repeats an entry is refused, before anything is written.
///
/// **A duplicate does not build two files, it builds one.** `fs::write` creates
/// or truncates, so `["A.olean", "A.olean"]` leaves a tree of size one. Every
/// fixture test here derives its expected count from the LIST -- the sorted and
/// helper-order tests compare against `CREATED.len()`, others against a literal
/// -- so the slip surfaces as "the walk must enumerate exactly N files". The
/// walk is then blamed for losing a file that was never written, and the person
/// reading that message goes to the walk, which is correct.
///
/// **It also poisons the shape record.** The manifest beside the tree would
/// store the entry twice, so a later run whose list had been tidied to one copy
/// would be refused as a shape change that never happened -- a second wrong
/// diagnosis downstream of the first.
///
/// **Planted, because the live population is clean.** No fixture list in this
/// file repeats an entry, so the guard would never run and a guard nothing
/// satisfies is indistinguishable from one that no longer works. The green
/// control comes first: a list holding two DIFFERENT entries that happen to
/// share a directory must still build both, or the rule would be refusing
/// neighbours rather than repeats.
#[test]
fn a_fixture_list_that_repeats_an_entry_is_refused() {
    // GREEN CONTROL FIRST. Two distinct entries under one directory, which is
    // the shape a too-eager rule would refuse.
    let ok = write_inventory_fixture(
        "t6r7-selftest-duplicate-ok-v1",
        &["Same/One.olean", "Same/Two.olean"],
    );
    for entry in ["Same/One.olean", "Same/Two.olean"] {
        assert!(
            ok.join(entry).is_file(),
            "`{entry}` is distinct from its sibling and must still be written"
        );
    }

    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let repeated = std::panic::catch_unwind(|| {
        write_inventory_fixture(
            "t6r7-selftest-duplicate-v1",
            &["Twice.olean", "Other.olean", "Twice.olean"],
        )
    });
    std::panic::set_hook(previous);

    let payload = repeated
        .err()
        .unwrap_or_else(|| panic!("a fixture list that names an entry twice must be refused"));
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap_or_default();

    // NAMES THE REPEAT, NOT MERELY THE FACT. "duplicate entry" would leave the
    // reader counting a list by eye, which is the work the guard exists to do.
    assert!(
        message.contains("Twice.olean"),
        "the refusal must name the entry that repeats: {message}"
    );
    assert!(
        message.contains("t6r7-selftest-duplicate-v1"),
        "the refusal must name the fixture: {message}"
    );
    // AND NOT THE INNOCENT ONE. A message listing the whole list would satisfy
    // the assertion above while telling the reader nothing about which line to
    // look at.
    assert!(
        !message.contains("Other.olean"),
        "the refusal names `Other.olean`, which appears once; a message that prints the whole \
         list has not located anything: {message}"
    );

    assert!(
        !Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join("t6r7-selftest-duplicate-v1")
            .exists(),
        "the list was refused and a tree exists anyway; the check must run BEFORE the writes, or \
         the half-built tree is left for the next run to union into"
    );
}

/// Two SPELLINGS of one path are one entry, and the duplicate guard used to
/// disagree.
///
/// **The guard compared strings; the filesystem compares paths.** `A.olean` and
/// `A.olean/` are different `&str`s and the same file: `Path` drops a trailing
/// separator when it splits into components, and drops a repeated one too, so
/// `A/B.olean` and `A//B.olean` are also one path. A set of strings sees two
/// entries where `base.join` sees one, both writes land on the same file, and
/// the tree comes out one smaller than the list -- which is precisely the
/// failure the duplicate guard was added to stop, walking through it because the
/// guard compared a rendering instead of the thing rendered.
///
/// **That is the third time in this file, and the shape is worth naming.** The
/// empty-component rule inspected the PATH's components while the name is made
/// of segments. The containment check compared a lexical prefix while the
/// question was about where a write lands. Here a set of strings stood in for a
/// set of paths. Each time the check was one representation away from its
/// subject, and each time it passed every test written for it.
///
/// **The mechanism is asserted, not described.** If `Path` ever stopped
/// collapsing these spellings, the guard would be solving a problem that no
/// longer exists and this test would say so instead of quietly passing.
///
/// **Both spellings must appear in the refusal.** Naming only the second leaves
/// the reader scanning the list for whichever other line means the same thing,
/// which is the whole work.
#[test]
fn two_spellings_of_one_path_are_one_fixture_entry() {
    // THE MECHANISM, LEXICALLY. Different strings, same file.
    let base = Path::new("/fixtures/tree");
    assert_ne!(
        "Same.olean", "Same.olean/",
        "the two spellings must differ as text, or there is nothing for a string set to miss"
    );
    assert_eq!(
        base.join("Same.olean"),
        base.join("Same.olean/"),
        "a trailing separator must not change which file is written, or this guard is about \
         nothing"
    );
    assert_eq!(
        base.join("A/B.olean"),
        base.join("A//B.olean"),
        "a repeated separator must not change which file is written either"
    );

    // GREEN CONTROL FIRST: two entries that differ AS PATHS must still build.
    let ok = write_inventory_fixture(
        "t6r7-selftest-spelling-ok-v1",
        &["Dir/One.olean", "Dir/Two.olean"],
    );
    for entry in ["Dir/One.olean", "Dir/Two.olean"] {
        assert!(
            ok.join(entry).is_file(),
            "`{entry}` names its own file and must still be written"
        );
    }

    let refuse = |name: &str, entries: &[&str]| -> String {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let outcome = std::panic::catch_unwind(|| write_inventory_fixture(name, entries));
        std::panic::set_hook(previous);
        let payload = outcome
            .err()
            .unwrap_or_else(|| panic!("`{entries:?}` name one file and must be refused"));
        payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .unwrap_or_default()
            .to_string()
    };

    let trailing = refuse(
        "t6r7-selftest-spelling-trailing-v1",
        &["Same.olean", "Same.olean/"],
    );
    let repeated = refuse(
        "t6r7-selftest-spelling-repeated-v1",
        &["A/B.olean", "A//B.olean"],
    );

    // BOTH SPELLINGS, delimited so the shorter one is not merely a substring of
    // the longer: `Same.olean` occurs inside `Same.olean/`, and a bare
    // `contains` would be satisfied by the longer alone.
    assert!(
        trailing.contains("`Same.olean`") && trailing.contains("`Same.olean/`"),
        "the refusal must name BOTH spellings; naming one leaves the reader scanning the list for \
         the other: {trailing}"
    );
    assert!(
        repeated.contains("`A/B.olean`") && repeated.contains("`A//B.olean`"),
        "the refusal must name both spellings of the repeated separator: {repeated}"
    );

    for name in [
        "t6r7-selftest-spelling-trailing-v1",
        "t6r7-selftest-spelling-repeated-v1",
    ] {
        assert!(
            !Path::new(env!("CARGO_TARGET_TMPDIR")).join(name).exists(),
            "`{name}` was refused and a tree exists anyway; the check must run before the writes"
        );
    }
}

/// An entry that is a file and another entry's parent directory is refused, the
/// same way whichever order it is listed in.
///
/// **The operating system already refuses it, in two different voices.**
/// `["Nested", "Nested/Leaf.olean"]` writes the file first and then dies in
/// `create_dir_all` with `Not a directory`. Swap the two and it creates the
/// directory first and dies in `fs::write` with `Is a directory`. One authoring
/// mistake, two diagnoses, selected by the order of a list nobody thinks of as
/// ordered -- and neither message mentions the entry it collides WITH, which is
/// the only fact that resolves it.
///
/// **So the refusal is asserted for BOTH orders, and asserted to be the same.**
/// A guard that only caught the order it was written against would leave the
/// other half exactly as it was, and the half it left is the one whose OS error
/// happens to be more plausible-looking.
///
/// **A third pair exists for a rule this test's own name invites.** Both pairs
/// above differ in depth by exactly one, so `outer_depth + 1 == inner_depth` --
/// "another entry's PARENT directory", read literally -- refuses both and passes
/// every assertion here. `Nested` beside `Nested/Deep/Leaf.olean` is the same
/// conflict two levels down, and the depth gap is asserted so the cell cannot
/// quietly become a fourth copy of the first.
///
/// **The green control is the one a string-prefix implementation fails.**
/// `Nested` is a prefix of `NestedOther.olean` as TEXT and not as a path: the
/// components are `Nested` and `NestedOther.olean`, which are simply different
/// names. `Path::starts_with` compares components, so the pair builds; a rule
/// written with `str::starts_with` would refuse a perfectly ordinary fixture and
/// nothing else here would notice.
#[test]
fn an_entry_that_is_also_another_entrys_directory_is_refused_in_either_order() {
    // GREEN CONTROL FIRST: a shared text prefix that is not a shared path.
    let ok = write_inventory_fixture(
        "t6r7-selftest-parent-ok-v1",
        &["Nested/Leaf.olean", "NestedOther.olean"],
    );
    for entry in ["Nested/Leaf.olean", "NestedOther.olean"] {
        assert!(
            ok.join(entry).is_file(),
            "`{entry}` shares only a text prefix with its sibling and must still be written"
        );
    }

    let refuse = |name: &str, entries: &[&str]| -> String {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let outcome = std::panic::catch_unwind(|| write_inventory_fixture(name, entries));
        std::panic::set_hook(previous);
        let payload = outcome
            .err()
            .unwrap_or_else(|| panic!("`{entries:?}` must be refused, not written"));
        payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .unwrap_or_default()
            .to_string()
    };

    let file_first = refuse(
        "t6r7-selftest-parent-file-first-v1",
        &["Nested", "Nested/Leaf.olean"],
    );
    let directory_first = refuse(
        "t6r7-selftest-parent-dir-first-v1",
        &["Nested/Leaf.olean", "Nested"],
    );
    // AN ANCESTOR THAT IS NOT THE DIRECT PARENT. Both pairs above differ in
    // depth by exactly one, so a rule written `outer_depth + 1 == inner_depth`
    // -- the reading this test's own name invites, "another entry's PARENT
    // directory" -- refuses both and survives everything below. The conflict is
    // the same: one path cannot be a file and an ancestor of another entry, at
    // any distance.
    let grandparent = refuse(
        "t6r7-selftest-parent-deep-v1",
        &["Nested", "Nested/Deep/Leaf.olean"],
    );

    // BOTH ENTRIES, IN BOTH ORDERS. Naming only one is what the filesystem
    // already did.
    for message in [&file_first, &directory_first] {
        assert!(
            message.contains("`Nested`") && message.contains("`Nested/Leaf.olean`"),
            "the refusal must name BOTH entries; the OS error it replaces named only one: \
             {message}"
        );
    }
    // AND THE SAME DIAGNOSIS EITHER WAY. Compared after stripping the fixture
    // names, which are the only part that legitimately differs between the two
    // calls.
    assert_eq!(
        file_first.replace("t6r7-selftest-parent-file-first-v1", "<fixture>"),
        directory_first.replace("t6r7-selftest-parent-dir-first-v1", "<fixture>"),
        "the two orders give different diagnoses for the same mistake, which is the behaviour \
         this guard exists to remove"
    );

    // THE DEPTH GAP IS TWO, SAID IN CODE. If this entry were ever shortened to a
    // direct child, the cell would go on passing while testing the same thing as
    // the two above.
    assert_eq!(
        Path::new("Nested/Deep/Leaf.olean").components().count()
            - Path::new("Nested").components().count(),
        2,
        "the deep entry must sit more than one level below the file it collides with, or it does \
         not distinguish a direct-parent rule from an ancestor rule"
    );
    assert!(
        grandparent.contains("`Nested`") && grandparent.contains("`Nested/Deep/Leaf.olean`"),
        "the grandparent refusal must name both entries: {grandparent}"
    );

    for name in [
        "t6r7-selftest-parent-file-first-v1",
        "t6r7-selftest-parent-dir-first-v1",
        "t6r7-selftest-parent-deep-v1",
    ] {
        assert!(
            !Path::new(env!("CARGO_TARGET_TMPDIR")).join(name).exists(),
            "`{name}` was refused and a tree exists anyway; the check must run BEFORE the writes, \
             or the conflicting file is already on disk when the refusal arrives"
        );
    }
}

/// The fixture NAME is validated, and it is the argument that decides where
/// everything goes.
///
/// **Three guards on the entries, none on the name.** An entry cannot escape the
/// tree, repeat itself, or claim to be both a file and another entry's parent.
/// `versioned_name` was joined straight onto the temporary directory and
/// formatted into the shape record's path with nothing looking at it -- and it
/// is the argument that decides where the tree and the record LAND, so it can do
/// strictly more damage than any entry.
///
/// **An empty name is the interesting one, because it fails silently.** It makes
/// the base the temporary directory itself -- the directory all 29 fixtures in
/// this file already share, which is what a batch run's tree shows. The
/// fixture's population becomes all of theirs: counts come back too high, and
/// nothing in the walk, the name registry or the shape record can see it -- the
/// union hazard those two exist to prevent, arriving through the parameter
/// neither inspects. The neighbouring fixture built below is the evidence that
/// the directory is not empty of oleans.
///
/// Cargo documents this directory as per-package, so other test binaries would
/// share it as well. That is the documentation's claim and not an observation of
/// mine: the only populated tree I looked at held fixtures from this file alone.
/// The argument does not need it.
///
/// **Three reasons, told apart.** A single "bad fixture name" message would let
/// any of the three pass in another's place, which is how a direction check goes
/// dark while every call site stays green.
///
/// **Only the separator case can assert that nothing was built.** The other two
/// resolve to directories that already exist -- the temporary directory and
/// `target/` -- so their absence proves nothing. Said rather than quietly
/// omitted.
///
/// **A fourth name exists because the non-ordinary branch had one decoy, and it
/// was a `..`.** A rule built around that reading -- the danger is a parent
/// directory -- refuses every name here and cannot be told apart from the real
/// one, which asks for an ordinary component and gets a ROOT. `/` is that input:
/// it round-trips through its own component, so the spelling half does not save
/// it either, and the tree it would name is the filesystem root.
#[test]
fn the_fixture_name_is_validated_and_it_decides_where_everything_lands() {
    let tmp = Path::new(env!("CARGO_TARGET_TMPDIR"));

    // GREEN CONTROL, WHICH DOUBLES AS THE EVIDENCE. An ordinary name builds --
    // and the file it leaves is exactly what a fixture rooted at the temporary
    // directory would pull into its own population.
    let ok = write_inventory_fixture("t6r7-selftest-name-ok-v1", &["Neighbour.olean"]);
    assert_eq!(ok, tmp.join("t6r7-selftest-name-ok-v1"));
    assert!(
        ok.join("Neighbour.olean").is_file(),
        "an ordinary fixture name must still build"
    );
    assert!(
        tmp.join("t6r7-selftest-name-ok-v1/Neighbour.olean")
            .is_file(),
        "this olean sits below the SHARED temporary directory. A fixture whose name was empty \
         would be rooted there and would count it as one of its own modules"
    );

    let refuse = |name: &str| -> String {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let outcome = std::panic::catch_unwind(|| write_inventory_fixture(name, &["Any.olean"]));
        std::panic::set_hook(previous);
        let payload = outcome
            .err()
            .unwrap_or_else(|| panic!("the fixture name `{name}` must be refused"));
        payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .unwrap_or_default()
            .to_string()
    };

    let empty = refuse("");
    let climbing = refuse("..");
    let nested = refuse("nested/name");

    // EACH ON THE WORDS UNIQUE TO ITS OWN BRANCH, and asserted absent from the
    // others: all three are refusals of a fixture name, so `is_err()` or a
    // shared fragment would let one cell pass on another's panic.
    assert!(
        empty.contains("names nothing at all") && !empty.contains("climb out"),
        "the empty name must be refused for having no components: {empty}"
    );
    assert!(
        climbing.contains("climb out") && !climbing.contains("path separator"),
        "`..` must be refused for leaving the temporary directory: {climbing}"
    );
    assert!(
        nested.contains("path separator") && !nested.contains("names nothing at all"),
        "`nested/name` must be refused for nesting: {nested}"
    );
    assert!(
        nested.contains("nested/name"),
        "the refusal must name the fixture it is about: {nested}"
    );

    // NOTHING WAS BUILT -- provable for this case only. `""` resolves to the
    // temporary directory and `..` to `target/`; both exist regardless, so their
    // absence would be no evidence at all.
    assert!(
        !tmp.join("nested").exists(),
        "`nested/name` was refused and a tree appeared anyway; the name check must run before \
         anything is created"
    );

    // THE NON-ORDINARY BRANCH HAS ONE DECOY AND IT IS A `..`. A rule written
    // around that -- "the danger is a parent directory" -- refuses `..`, and
    // refuses the other three for their own reasons, so nothing here tells it
    // apart from the real rule. `/` is the input that does: its single component
    // is a ROOT, not a parent.
    assert!(
        matches!(
            Path::new("..").components().next(),
            Some(std::path::Component::ParentDir)
        ),
        "the existing decoy must be a parent-directory component, or the gap described here is \
         not the gap that exists"
    );
    assert!(
        matches!(
            Path::new("/").components().next(),
            Some(std::path::Component::RootDir)
        ),
        "`/` must be a ROOT component; that is what a rule aimed at `..` does not cover"
    );
    // AND THE SPELLING HALF DOES NOT SAVE IT: `/` is exactly its own component,
    // so a name that round-trips can still be catastrophic.
    assert_eq!(
        Path::new("/").components().next().map(|c| c.as_os_str()),
        Some(std::ffi::OsStr::new("/")),
        "`/` round-trips through its own component, so only the ORDINARY-name rule refuses it"
    );
    assert_eq!(
        tmp.join("/"),
        Path::new("/"),
        "an absolute name discards the temporary directory: the fixture tree would be the \
         filesystem root, and the walk would enumerate it"
    );

    let rooted = refuse("/");
    assert!(
        rooted.contains("climb out") && !rooted.contains("names nothing at all"),
        "`/` must be refused as a name that is not ordinary, not as one with no components: \
         {rooted}"
    );
    assert!(
        !Path::new("/.manifest").exists(),
        "the refusal must precede the shape record's write; a record for the name `/` would be \
         `/.manifest`, at the filesystem root"
    );
}

/// A name that PARSES as one component is not the same as one SPELLED that way.
///
/// **The name is read as a path and used as a string.** The rule added with the
/// name check asks `Path::components()` for exactly one `Normal`. The shape
/// record is built with `format!("{name}.manifest")`. `Spelled/` satisfies the
/// path reading and breaks the string one: the tree is `<tmp>/Spelled`, the
/// record is `<tmp>/Spelled/.manifest` -- INSIDE the tree instead of beside it,
/// which is exactly what the manifest test's sibling assertion exists to
/// prevent. A record inside a fixture joins every walk of it.
///
/// **And the two guards that would catch it are the two it slips past.**
/// `Spelled` and `Spelled/` name the same tree, because `Path` equality is by
/// components. They are different registry keys, because that map is keyed by
/// the string. They have different record paths, because those are formatted
/// from the string too. So two fixtures could share one tree while the name
/// registry and the shape record each see two unrelated fixtures -- the precise
/// situation both were written to make impossible.
///
/// **Fourth instance of one shape, arriving through the parameter hardened last
/// time.** The empty-component rule inspected the path's components while the
/// name is made of segments; the containment check compared a lexical prefix
/// while the question was where a write lands; the duplicate guard keyed a set
/// on strings while the filesystem keys on paths. Here the same argument is read
/// one way and written another, and the check I added for it a few commits ago
/// only covered the reading.
///
/// **Every claim here is asserted lexically**, so nothing rests on my having
/// read `Path`'s documentation correctly.
///
/// **A second spelling exists for the cheap version of this rule.** `Spelled/`
/// is refused by the round-trip test AND by "reject a name ending in a
/// separator", so it cannot distinguish them. `Spelled/.` is the input that can:
/// it ends in a dot, the cheap rule takes it, `Path` still collapses it to one
/// component, and its record still lands inside the tree. Measured across both
/// rules and all the old inputs before the cell was written -- the discriminating
/// input has to be shown to be discriminating, or it is just a third example.
#[test]
fn a_fixture_name_must_be_spelled_as_one_component_not_merely_parse_as_one() {
    let tmp = Path::new(env!("CARGO_TARGET_TMPDIR"));

    // THE MECHANISM, IN FOUR LINES, NO FILESYSTEM. One tree, two spellings; and
    // the record beside it for one spelling and inside it for the other.
    assert_eq!(
        tmp.join("Spelled/"),
        tmp.join("Spelled"),
        "the two spellings must name the SAME tree, or there is no shared tree for the registry \
         to miss"
    );
    assert_ne!(
        "Spelled/", "Spelled",
        "and they must differ as text, or the registry could not key them apart"
    );
    assert!(
        tmp.join("Spelled/.manifest")
            .starts_with(tmp.join("Spelled/")),
        "the trailing spelling must put the shape record INSIDE the tree; that is the whole \
         defect"
    );
    assert!(
        !tmp.join("Spelled.manifest")
            .starts_with(tmp.join("Spelled")),
        "the ordinary spelling must keep the record beside the tree, or the fix has no green side"
    );

    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let outcome = std::panic::catch_unwind(|| write_inventory_fixture("Spelled/", &["Any.olean"]));
    std::panic::set_hook(previous);
    let payload = outcome
        .err()
        .unwrap_or_else(|| panic!("a name that only parses as one component must be refused"));
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap_or_default();

    // ON THE WORDS UNIQUE TO THIS BRANCH. The name check has four reasons now
    // and they share a sentence shape; a cell that only asserted "refused" would
    // pass on any of the other three.
    assert!(
        message.contains("not spelled as one"),
        "the refusal must be about the spelling, not about the name having no components or \
         climbing out: {message}"
    );
    assert!(
        !message.contains("names nothing at all") && !message.contains("climb out"),
        "this must not be passing on a sibling branch's refusal: {message}"
    );

    assert!(
        !tmp.join("Spelled").exists(),
        "the name was refused and its tree exists anyway; the check must run before anything is \
         created"
    );

    // THE SPELLING THAT A TRAILING-SLASH TEST WOULD LET THROUGH. `Spelled/` is
    // refused by the rule above AND by the cheap version of it -- reject a name
    // that ends in a separator -- so it cannot tell the two apart. `Spelled/.`
    // ends in a dot: the cheap rule accepts it, the round-trip rule refuses it,
    // and the harm is identical. Measured, all three columns, before this cell
    // was written.
    assert!(
        !"Spelled/.".ends_with('/'),
        "the discriminating name must NOT end in a separator, or the cheap rule refuses it too and \
         this cell proves nothing"
    );
    assert!(
        tmp.join("Spelled/..manifest")
            .starts_with(tmp.join("Spelled/.")),
        "this spelling must put the record inside the tree as well; a discriminating input that \
         did no harm would be a rule for its own sake"
    );

    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let outcome = std::panic::catch_unwind(|| write_inventory_fixture("Spelled/.", &["Any.olean"]));
    std::panic::set_hook(previous);
    let payload = outcome.err().unwrap_or_else(|| {
        panic!("`Spelled/.` parses as one component and is not spelled as one; it must be refused")
    });
    let dotted = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap_or_default();
    assert!(
        dotted.contains("not spelled as one"),
        "the dot spelling must be refused by the SAME branch as the slash spelling, not by the \
         one about a name having no components: {dotted}"
    );
    assert!(
        !tmp.join("Spelled").exists(),
        "`Spelled/.` names the same directory as `Spelled`, and it was refused, so nothing may \
         have been created there"
    );
}

/// Re-spelling an entry is not a change of shape, and both records used to say
/// it was.
///
/// **One argument, three keys.** The duplicate guard keys entries on the PATH,
/// because that is what the filesystem keys on. The name registry and the shape
/// record keyed on the STRING. So the same list was read three ways inside one
/// function, and the two string readings answered a question about spelling
/// while claiming to answer one about the tree.
///
/// **The symptom is a false alarm, which is why it would have been believed.**
/// `Dir//One.olean` and `Dir/One.olean` produce exactly the same file. Building
/// a fixture with one and then the other made the registry report a fixture
/// "built twice with different contents" and the record report a shape change --
/// two accusations of a collision, about a build that changed nothing. A guard
/// that cries wolf about a no-op is worse than one that stays quiet: the next
/// person to see it learns to widen the guard.
///
/// **This closes the class rather than patching a fifth instance.** Entries are
/// collapsed to one canonical form up front, and the registry, the record and
/// the writes all use it. There is now a single answer to "which file does this
/// entry name", instead of three that agree only while nobody spells anything
/// unusually.
///
/// **And the guards must still fire on a real difference**, or this would be a
/// weakening dressed as a fix. The last cell asks for a genuinely different list
/// under the same name and requires the registry to refuse it.
#[test]
fn re_spelling_an_entry_is_not_a_change_of_shape() {
    const NAME: &str = "t6r7-selftest-respelled-v1";
    let tmp = Path::new(env!("CARGO_TARGET_TMPDIR"));

    // THE MECHANISM: different text, one file.
    assert_ne!("Dir/One.olean", "Dir//One.olean");
    assert_eq!(
        tmp.join("Dir/One.olean"),
        tmp.join("Dir//One.olean"),
        "the two spellings must name one file, or there is no false alarm to remove"
    );

    let first = write_inventory_fixture(NAME, &["Dir/One.olean"]);
    // The same tree, spelled differently. Before this commit the registry
    // refused this call outright.
    let second = write_inventory_fixture(NAME, &["Dir//One.olean"]);
    assert_eq!(
        first, second,
        "the two builds must return the same tree, because they ARE the same tree"
    );
    assert!(
        first.join("Dir/One.olean").is_file(),
        "the entry must be written once, under its canonical spelling"
    );

    // THE RECORD HOLDS THE CANONICAL FORM, so a later run spelled either way
    // matches it. A record holding `Dir//One.olean` would refuse the ordinary
    // spelling on the next run.
    let recorded = fs::read_to_string(tmp.join(format!("{NAME}.manifest")))
        .unwrap_or_else(|error| panic!("read the shape record: {error}"));
    assert_eq!(
        recorded, "Dir/One.olean",
        "the shape record must hold the canonical form of the REQUEST, not the spelling it was \
         asked for. It does not describe the tree -- see \
         `the_shape_record_is_of_the_request_not_of_the_tree`, which this message used to \
         overstate"
    );

    // AND A REAL DIFFERENCE IS STILL REFUSED. Without this, everything above is
    // satisfied by a registry that stopped comparing anything at all.
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let genuinely_different =
        std::panic::catch_unwind(|| write_inventory_fixture(NAME, &["Dir/Two.olean"]));
    std::panic::set_hook(previous);
    let payload = genuinely_different
        .err()
        .unwrap_or_else(|| panic!("a different list under one name must still be refused"));
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap_or_default();
    assert!(
        message.contains("Dir/Two.olean") && message.contains("Dir/One.olean"),
        "the refusal must still name both file sets: {message}"
    );
}

/// The shape record is of the REQUEST, not of the tree.
///
/// **Five fixtures already disagree with their own record.** Two add a symlink
/// after the writer returns, one adds a file whose name is not UTF-8, and two
/// add an over-cap sparse file and a small one. Three of those five compile only
/// on unix, so the count is five there and two everywhere -- said precisely
/// because "five fixtures" is the kind of number that gets quoted. The writer
/// never saw any of them, so the record does not mention them, and a walk of
/// those trees does.
/// The record and the tree are different objects, and the record's question is
/// "was this name last built from this list", which is the one the union hazard
/// turns on.
///
/// **The message next door used to say otherwise, and this test is why it does
/// not.** It read "the shape record must describe the tree", which is false of
/// five live fixtures. A guard's scope is exactly the kind of claim that gets
/// widened in prose and then relied on.
///
/// **Pinned so the boundary is not "improved" away.** Strengthening the record
/// into a hash of the tree is an obvious-looking upgrade and would redden every
/// fixture that adds a file by hand -- for a hazard the record was never written
/// to catch. If someone does it deliberately, this test is where they say so.
///
/// **The disagreement is exhibited, not described**: the walk finds two modules
/// in a tree whose record names one.
#[test]
fn the_shape_record_is_of_the_request_not_of_the_tree() {
    const NAME: &str = "t6r7-selftest-record-scope-v1";
    let library = write_inventory_fixture(NAME, &["Declared.olean"]);

    // A file the writer never heard of, exactly as five real fixtures do.
    fs::write(library.join("Undeclared.olean"), b"")
        .unwrap_or_else(|error| panic!("add an undeclared entry: {error}"));

    // REBUILDING IS STILL ACCEPTED. The record cannot see the extra file, so the
    // same list is the same shape -- and nothing removes the file either,
    // because the writer only ever creates or truncates what it was asked for.
    let again = write_inventory_fixture(NAME, &["Declared.olean"]);
    assert_eq!(again, library, "the rebuild must return the same tree");
    assert!(
        library.join("Undeclared.olean").is_file(),
        "the rebuild must leave a file it was never told about; the writer creates, it does not \
         sweep"
    );

    let recorded =
        fs::read_to_string(Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("{NAME}.manifest")))
            .unwrap_or_else(|error| panic!("read the shape record: {error}"));
    assert_eq!(
        recorded, "Declared.olean",
        "the record holds the request it was given"
    );
    assert!(
        !recorded.contains("Undeclared"),
        "the record must NOT have grown to describe the tree: {recorded}"
    );

    // THE DISAGREEMENT, EXHIBITED. Two modules in a tree whose record names one.
    let walked = walk_olean_inventory(&library, Some("Fixture"))
        .unwrap_or_else(|reason| panic!("the tree must walk: {reason}"));
    assert_eq!(
        walked.modules.len(),
        2,
        "the WALK sees both files while the record knows one; that gap is the point of this test, \
         and it is what a tree-hashing record would remove along with five working fixtures: {:?}",
        walked.modules
    );
}

/// A shape record that cannot be read is not a shape record that is absent.
///
/// **The reader was `if let Ok(...)`, so every error meant "never built".** A
/// record that exists and cannot be decoded disabled the guard completely: the
/// build went ahead on whatever list it was handed, and the write that follows
/// replaced the record -- so the run destroyed the only evidence that anything
/// had been wrong. Silent and self-erasing, which is the worst pair.
///
/// **I had already argued this distinction, three commits before writing it the
/// other way.** The retained-receipt reader separates a file that is not there
/// from one it cannot read, for exactly this reason. Knowing a rule and applying
/// it are different acts, and nothing in my own process caught the second
/// instance.
///
/// **Absent earns the quiet arm and nothing else does.** A first build has no
/// record and must proceed; that is the ordinary case and nobody can fix it from
/// the repository. Every other error is a fault about a file that is sitting
/// right there.
///
/// **Demonstrated on a planted corrupt record**, with the corruption asserted to
/// be real -- a lone invalid byte, which is what a half-finished write leaves --
/// so the unreadable arm is not being exercised by a file that is merely
/// unusual. And the record is asserted to SURVIVE the refusal: a guard that
/// refuses and then overwrites has still destroyed the evidence.
#[test]
fn a_shape_record_that_cannot_be_read_is_not_an_absent_one() {
    const NAME: &str = "t6r7-selftest-record-corrupt-v1";
    let manifest = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("{NAME}.manifest"));

    // A lone invalid byte, which is what a half-finished write leaves.
    const CORRUPT: [u8; 3] = [b'{', 0xFF, b'}'];
    fs::write(&manifest, CORRUPT)
        .unwrap_or_else(|error| panic!("plant the corrupt record: {error}"));

    // THE PRECONDITION IS ABOUT THE FILE, NOT ABOUT A LITERAL, and it is read
    // back from disk to say so. Asserting that the constant fails to decode is
    // something the compiler folds away -- it warns that the call can only ever
    // fail -- which is a statement about the source text rather than about the
    // record the guard will meet.
    let planted = fs::read(&manifest).unwrap_or_else(|error| panic!("re-read the plant: {error}"));
    assert!(
        String::from_utf8(planted).is_err(),
        "the planted record must genuinely fail to decode, or this test exercises the readable \
         arm under another name"
    );

    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let outcome = std::panic::catch_unwind(|| write_inventory_fixture(NAME, &["Any.olean"]));
    std::panic::set_hook(previous);

    let payload = outcome
        .err()
        .unwrap_or_else(|| panic!("a record that cannot be read must not be treated as absent"));
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap_or_default();
    assert!(
        message.contains("could not be read"),
        "the refusal must say the record is unreadable, not that the shape changed: {message}"
    );
    assert!(
        message.contains(NAME),
        "the refusal must name the fixture: {message}"
    );

    // THE EVIDENCE SURVIVES. The record is written before the tree, so a guard
    // that refused after writing it would have replaced the corrupt bytes with a
    // tidy record of the very build it was refusing.
    assert_eq!(
        fs::read(&manifest).unwrap_or_else(|error| panic!("re-read the record: {error}")),
        CORRUPT,
        "the corrupt record was overwritten by the run that refused it; the fault is now \
         unreproducible and the next run will see a record it wrote itself"
    );
    assert!(
        !Path::new(env!("CARGO_TARGET_TMPDIR")).join(NAME).exists(),
        "nothing may be built when the record cannot be read"
    );

    // GREEN CONTROL: an ABSENT record must still build. Without this the fix
    // could be refusing every first build in the file and this test would not
    // know.
    let fresh = write_inventory_fixture("t6r7-selftest-record-absent-v1", &["Any.olean"]);
    assert!(
        fresh.join("Any.olean").is_file(),
        "a fixture with no record yet is an ordinary first build and must proceed"
    );
}

/// A fixture's TREE must not be another fixture's shape RECORD.
///
/// **One directory holds both kinds of object.** The record for `X` is
/// `<tmp>/X.manifest`; a fixture named `X.manifest` would put its tree at that
/// same path. Both names satisfy every naming rule -- one ordinary component,
/// spelled as one -- so nothing stopped them, and the two objects then fight
/// over one path.
///
/// **The collision is computed here, not asserted from memory.** The test builds
/// an ordinary fixture, reads back where its record actually went, and requires
/// the reserved name to be exactly that path's file name. If the record's naming
/// scheme ever changes, this test stops agreeing with itself instead of
/// continuing to guard a path nothing uses.
///
/// **Order decides which failure you see, which is the tell.** Build `X` first
/// and the record is a file, so the other fixture's `create_dir_all` dies with a
/// raw `Not a directory`. Build `X.manifest` first and the record path is a
/// directory, so `X`'s record read fails and is refused as unreadable -- true,
/// and pointing at the wrong cause. A naming problem should not be diagnosed by
/// whichever test happened to run first.
///
/// **The green control is the one a `contains` implementation fails.** A name
/// that merely mentions the word must still build; only the suffix is reserved.
///
/// **A second refused name exists because the first is a LIVE collision.** Its
/// owner has been built, so a rule that refused only what actually clashes --
/// "is there really something at that path?" -- refuses it too and cannot be
/// told apart from a reservation. The second name's owner has never been built,
/// so a collision check sees nothing to protect, and it must still be refused:
/// build order is not fixed, and letting the record path be taken first is what
/// produces the order-dependent failure this rule was written to remove.
#[test]
fn a_fixture_tree_may_not_sit_where_another_fixtures_record_does() {
    let tmp = Path::new(env!("CARGO_TARGET_TMPDIR"));

    // WHERE THE RECORD ACTUALLY GOES, read off a real build rather than assumed.
    const OWNER: &str = "t6r7-selftest-reserved-v1";
    write_inventory_fixture(OWNER, &["Any.olean"]);
    let record = tmp.join(format!("{OWNER}.manifest"));
    assert!(
        record.is_file(),
        "the owning fixture's record must exist for this collision to be real: {}",
        record.display()
    );
    let reserved = record
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or_else(|| panic!("the record path has no usable file name"))
        .to_string();

    // GREEN CONTROL FIRST: mentioning the word is not the same as ending with
    // it. A rule written with `contains` would refuse this.
    let ok = write_inventory_fixture("t6r7-manifest-ish-v1", &["Any.olean"]);
    assert!(
        ok.join("Any.olean").is_file(),
        "a name that merely mentions the record's word must still build"
    );

    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let outcome = std::panic::catch_unwind(|| write_inventory_fixture(&reserved, &["Any.olean"]));
    std::panic::set_hook(previous);

    let payload = outcome.err().unwrap_or_else(|| {
        panic!("`{reserved}` would put its tree on top of `{OWNER}`'s record and must be refused")
    });
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap_or_default();
    assert!(
        message.contains("shape record uses"),
        "the refusal must be about the reserved suffix, not about the name's shape: {message}"
    );
    assert!(
        message.contains(&reserved),
        "the refusal must name the fixture it is about: {message}"
    );

    // AND THE OWNER'S RECORD IS UNTOUCHED. A refusal that arrived after
    // `create_dir_all` would have replaced a working fixture's record with a
    // directory.
    assert!(
        record.is_file(),
        "the owning fixture's record is no longer a file; the refusal came too late"
    );
    assert!(
        !tmp.join(&reserved).is_dir(),
        "a tree was created at the record's path"
    );

    // THE SUFFIX IS RESERVED, NOT MERELY CONTESTED. The decoy above is the
    // record name of a fixture that ALREADY EXISTS, so a rule that refused only
    // a live collision -- "is there really something at that path?" -- refuses
    // it exactly as this one does and cannot be told apart. The name below ends
    // in the same suffix and its owner has never been built, so a collision
    // check sees nothing to protect.
    //
    // It must still be refused, because build order is not fixed. Let
    // `t6r7-never-built-v1.manifest` take that path today and the fixture it
    // belongs to may be added tomorrow -- and then which of the two fails, and
    // how, depends on which ran first. That is the order-dependent diagnosis
    // this rule exists to remove, and a collision check cannot remove it,
    // because at the moment of the first build there is no collision yet.
    const UNOWNED: &str = "t6r7-never-built-v1.manifest";
    const WOULD_OWN: &str = "t6r7-never-built-v1";

    // THE DISCRIMINATING PROPERTY, READ OFF THE DISK. If the owner ever were
    // built, a collision check would refuse this too and the cell would stop
    // distinguishing anything.
    assert!(
        !tmp.join(WOULD_OWN).exists(),
        "`{WOULD_OWN}` must NOT exist, or this name is a live collision like the one above and \
         proves nothing about reservation"
    );
    assert!(
        !tmp.join(UNOWNED).exists(),
        "`{UNOWNED}` must not already be on disk before the refusal is asked for"
    );

    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let outcome = std::panic::catch_unwind(|| write_inventory_fixture(UNOWNED, &["Any.olean"]));
    std::panic::set_hook(previous);
    let payload = outcome.err().unwrap_or_else(|| {
        panic!("`{UNOWNED}` takes a reserved record path and must be refused even with no owner")
    });
    let unowned = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap_or_default()
        .to_string();
    assert!(
        unowned.contains("shape record uses"),
        "an unowned record name must be refused for the RESERVATION, not for anything else: \
         {unowned}"
    );
    assert!(
        unowned.contains(UNOWNED),
        "the refusal must name the fixture it is about: {unowned}"
    );
    assert!(
        !tmp.join(UNOWNED).exists(),
        "the name was refused and a tree appeared anyway at the reserved path"
    );
}

/// A file named `.olean` is not an olean, and it is the only input that proves
/// the filter is about the EXTENSION.
///
/// **The existing exactness decoys cannot kill the obvious wrong filter.**
/// `the_inventory_vectors_are_parallel_and_the_extension_match_is_exact` plants
/// `Ignored.OLEAN` and `NoExtension` and requires both to be skipped. Replace
/// `path.extension() == Some("olean")` with `file_name().ends_with(".olean")` --
/// the change anyone would make without thinking -- and that test still passes:
/// `Ignored.OLEAN` differs in case, `NoExtension` has no dot, and both filters
/// reject both. The mutant survives every assertion in this file.
///
/// **`.olean` is the discriminating input, measured.** `Path::extension` returns
/// `None` for a name that begins with a dot and has no other, so the real filter
/// skips it; the suffix test sees `.olean` ending in `.olean` and takes it. One
/// file, opposite answers, and it was in no fixture.
///
/// **What the wrong filter would then do is worse than a miscount.** `.olean`
/// strips to `.olean` -- there is no extension to remove -- so it projects to a
/// module named `Fixture..olean`, whose middle segment has no characters. The
/// walk refuses that, so the mutant does not quietly count one module too many:
/// it makes the whole tree unwalkable, and the failure names an empty segment
/// rather than the filter that admitted the file. This test kills it at the
/// walk, where the cause is still visible.
///
/// **The decoy is asserted to be on disk**, because "a file that is not there
/// was not collected" is a sentence about nothing.
#[test]
fn a_dotfile_named_like_an_extension_is_not_an_olean() {
    // THE MECHANISM, LEXICALLY. The two filters agree on the old decoys and
    // disagree here, which is the entire reason this fixture exists.
    for (name, is_olean) in [(".olean", false), ("Real.olean", true)] {
        assert_eq!(
            Path::new(name)
                .extension()
                .and_then(|extension| extension.to_str())
                == Some("olean"),
            is_olean,
            "`{name}` must be judged by its EXTENSION"
        );
        assert!(
            name.ends_with(".olean"),
            "`{name}` must end with the suffix, or it does not distinguish the two filters"
        );
    }
    for decoy in ["Ignored.OLEAN", "NoExtension"] {
        assert!(
            !decoy.ends_with(".olean"),
            "`{decoy}` is rejected by the suffix filter too, which is why the older test cannot \
             tell the two apart"
        );
    }

    let library = write_inventory_fixture("t6r7-inventory-dotfile-v1", &["Real.olean", ".olean"]);
    assert!(
        library.join(".olean").is_file(),
        "the decoy must be on disk; `a file that is not there was not collected` states nothing"
    );

    let OleanInventory { oleans, modules } = walk_olean_inventory(&library, Some("Fixture"))
        .unwrap_or_else(|reason| {
            panic!(
                "the tree must walk. A filter matching the `.olean` SUFFIX would have collected \
                 the dotfile, projected it to a name with an empty segment, and failed here \
                 instead: {reason}"
            )
        });

    assert_eq!(
        oleans.len(),
        1,
        "only `Real.olean` is an olean; a leading-dot name has no extension at all: {oleans:?}"
    );
    assert_eq!(
        modules,
        vec!["Fixture.Real".to_string()],
        "the dotfile must contribute no module"
    );
}

/// The walk and `module_names_below` are now two implementations of one meaning,
/// and they must still agree.
///
/// **Splitting them is what makes this assertion worth anything.** Until this
/// commit the walk CALLED `module_names_below`, so comparing the two compared a
/// value with itself -- the definition of a vacuous test. The walk now projects
/// the paths it already collected, which removes a second `read_dir` sweep of
/// the same tree and makes `modules[i]` the projection of `oleans[i]` by
/// construction. The cost of that is a second copy of the same rule.
///
/// **And the second copy is not dead code.** `module_names_below` still has a
/// caller: the corpus inventory reads `mathlib_modules` through it. So the two
/// paths that name a module -- the one every fixture test exercises and the one
/// the corpus lane uses -- are now separate, and nothing else in this file would
/// notice if they drifted. A module named one way here and another way there
/// resolves against no import, which reads downstream as a corpus with missing
/// imports rather than as two projections disagreeing.
///
/// **The tree spans the cases that could distinguish them**: a top-level module,
/// a nested one, a directory whose name carries a dot, and a parent module --
/// the shape where path order and name order disagree, which is where two
/// differently-ordered implementations would part company.
#[test]
fn the_walks_two_module_name_paths_still_agree() {
    let library = write_inventory_fixture(
        "t6r7-two-projections-v1",
        &[
            "Top.olean",
            "Algebra.olean",
            "Algebra/Group.olean",
            "Mid.dotted/Leaf.olean",
        ],
    );

    let walked = walk_olean_inventory(&library, Some("Fixture"))
        .unwrap_or_else(|reason| panic!("the fixture must walk: {reason}"));
    let separately = module_names_below(&library, Some("Fixture"))
        .unwrap_or_else(|reason| panic!("the helper must enumerate: {reason}"));

    // ANTI-VACUITY FIRST. Comparing two empty vectors, or two one-element ones,
    // says nothing about ORDER -- and order is the half most likely to drift
    // once the two are separate.
    assert_eq!(
        walked.modules.len(),
        4,
        "the fixture's four modules must all be named: {:?}",
        walked.modules
    );
    assert!(
        walked
            .modules
            .iter()
            .any(|name| name.matches('.').count() >= 3),
        "the tree must span a nested module, or agreement over flat names says nothing about how \
         either side joins components: {:?}",
        walked.modules
    );

    assert_eq!(
        walked.modules, separately,
        "the walk's own projection and `module_names_below` disagree. They are two copies of one \
         rule since the walk stopped calling the helper, and only the corpus lane uses the \
         helper -- so a drift here would show up as a corpus whose imports resolve against \
         nothing, not as a naming bug"
    );
}

/// The shape is recorded BEFORE the tree is built, so a build that dies partway
/// still leaves something to compare against.
///
/// **The record used to be written last, and that is the one window where it
/// matters.** A completed build is indistinguishable under either order: the
/// tree and the record are both there. The difference appears only when the
/// build dies mid-way -- the disk filling under it, which happened twice while
/// this file was being written -- and the old order then left a PARTIAL tree and
/// no record at all. The next run had nothing to compare against, built whatever
/// its list said, and unioned into the leftovers: exactly the hazard the record
/// exists to stop, surviving precisely where it was needed.
///
/// **Observed by making the per-entry write a parameter.** No allocation
/// counter, no timing, no crashed process: the test hands over a writer that
/// succeeds once and then fails, which is what a disk filling looks like from
/// inside this function. If the record were still written last, it would not be
/// on disk when the panic escapes and the assertion below fails.
///
/// **The tree really is partial, and that is asserted too.** A writer that
/// failed on the FIRST entry would leave an empty tree, which is a different and
/// far less interesting situation -- nothing to union into. The first entry must
/// have landed and the second must not.
///
/// **And the retry completes it.** With the shape recorded, building the same
/// list again is allowed by both the name registry and the shape check, and the
/// tree finishes. That is the behaviour the ordering buys, so it is checked
/// rather than described.
#[test]
fn the_shape_is_recorded_before_the_tree_is_built() {
    const NAME: &str = "t6r7-selftest-record-first-v1";
    const ENTRIES: [&str; 2] = ["First.olean", "Second.olean"];

    let tmp = Path::new(env!("CARGO_TARGET_TMPDIR"));
    let manifest = tmp.join(format!("{NAME}.manifest"));
    let base = tmp.join(NAME);

    // A writer that succeeds once and then fails, held in an atomic so the
    // closure stays unwind-safe across `catch_unwind`.
    let attempts = std::sync::atomic::AtomicUsize::new(0);
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let outcome = std::panic::catch_unwind(|| {
        write_inventory_fixture_with(NAME, &ENTRIES, |path| {
            if attempts.fetch_add(1, std::sync::atomic::Ordering::Relaxed) == 0 {
                fs::write(path, b"")
            } else {
                Err(std::io::Error::other("simulated ENOSPC"))
            }
        })
    });
    std::panic::set_hook(previous);

    let payload = outcome
        .err()
        .unwrap_or_else(|| panic!("the injected writer must fail the second entry"));
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap_or_default();
    assert!(
        message.contains("Second.olean") && message.contains("simulated ENOSPC"),
        "the failure must name the entry that could not be written and why: {message}"
    );

    // THE TREE IS PARTIAL. Without this the assertion below would hold for a
    // build that never started, which is not the situation this is about.
    assert!(
        base.join("First.olean").is_file(),
        "the first entry must have landed, or there is no partial tree to protect"
    );
    assert!(
        !base.join("Second.olean").exists(),
        "the second entry must NOT have landed, or the writer was not injected. This fixture is \
         never retried, precisely so this stays true on every run"
    );
    assert_eq!(
        attempts.load(std::sync::atomic::Ordering::Relaxed),
        2,
        "the writer must have been REACHED for both entries; a build that stopped before the \
         second would leave the same partial tree for a different reason"
    );

    // THE RECORD SURVIVED THE FAILURE. Under the old order it would not exist at
    // all, and the next run would union into the partial tree above without
    // anything noticing.
    let recorded = fs::read_to_string(&manifest)
        .unwrap_or_else(|error| panic!("read {}: {error}", manifest.display()));
    assert_eq!(
        recorded, "First.olean\nSecond.olean",
        "the shape must be recorded before the build, and must describe what was ATTEMPTED"
    );

    // THE RETRY IS A SEPARATE FIXTURE, AND THAT IS NOT TIDiness. Nothing sweeps
    // these trees, so a retry here would leave `Second.olean` on disk and the
    // partial-tree assertion above would fail on the NEXT run -- with the tree
    // it was asserting the absence of created by its own previous pass. The two
    // properties cannot share a fixture: one needs the second entry never to
    // have been written, the other needs it eventually written.
    let resume_name = "t6r7-selftest-record-resume-v1";
    let resume_attempts = std::sync::atomic::AtomicUsize::new(0);
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let failed = std::panic::catch_unwind(|| {
        write_inventory_fixture_with(resume_name, &ENTRIES, |path| {
            if resume_attempts.fetch_add(1, std::sync::atomic::Ordering::Relaxed) == 0 {
                fs::write(path, b"")
            } else {
                Err(std::io::Error::other("simulated ENOSPC"))
            }
        })
    });
    std::panic::set_hook(previous);
    assert!(
        failed.is_err(),
        "the resume fixture must fail before it is resumed"
    );

    // AND THE RETRY COMPLETES THE TREE. Same name, same list: allowed by the
    // registry, matched by the record the failed build left behind, finished by
    // the ordinary writer. That is the behaviour the ordering buys.
    let resumed = write_inventory_fixture(resume_name, &ENTRIES);
    assert_eq!(resumed, tmp.join(resume_name));
    for entry in ENTRIES {
        assert!(
            resumed.join(entry).is_file(),
            "`{entry}` must exist after the retry; a recorded shape is what lets a failed build be \
             resumed instead of refused"
        );
    }
}

/// Add a symlink to a fixture tree, idempotently and without removing anything.
///
/// `symlink` fails with `AlreadyExists` on a second run, and these fixtures are
/// never swept, so the link is created only when nothing is there. Existence is
/// tested with `symlink_metadata`, which does NOT follow links -- `Path::exists`
/// follows, so a dangling link would read as absent and the creation would then
/// fail on the next run.
#[cfg(unix)]
fn link_fixture_entry(link: &Path, target: &Path) {
    if fs::symlink_metadata(link).is_ok() {
        return;
    }
    std::os::unix::fs::symlink(target, link).unwrap_or_else(|error| {
        panic!(
            "create fixture symlink {} -> {}: {error}",
            link.display(),
            target.display()
        )
    });
}

/// When a run is BOTH unsound and restrictive, the row must say UNSOUND.
///
/// **The one input combination nobody had evaluated.** `whole_mathlib_class`
/// takes two counts, so it has four cases. The guard's mutants cover
/// `(0, restrictive)` and `(unsound, 0)`, and the producer covers `(0, 0)`.
/// `(unsound, restrictive)` -- both nonzero -- had never been evaluated anywhere,
/// and it is the only one where the function has to CHOOSE.
///
/// **What the choice decides.** D23 is the asymmetry this entire bead rests on:
/// restrictive divergences are repairable findings, while accepting what the
/// Reference rejects is release-blocking and has no carve-out. A run exhibiting
/// both is release-blocking. If the precedence were inverted -- or if it were an
/// accident of which `if` came first, which is what an untested branch order is
/// -- such a run would be filed as `refuted_this_run_found_a_restrictive_divergence`,
/// and the single most serious result this lane can produce would be recorded as
/// the ordinary kind. Nothing downstream re-derives it: the class token is what
/// the retention guard reads and what a reader quotes.
///
/// **The protection is asserted through `validate`, not just the classifier.**
/// Getting the token right in the producer means nothing if the guard would
/// ACCEPT a row that downgraded it, since rows can be hand-written into the
/// retained file. So the same both-nonzero population is offered to the guard
/// three ways: with the unsound token it must pass, and with either the
/// restrictive or the clean token it must be refused.
#[test]
fn an_unsound_run_that_is_also_restrictive_is_filed_as_unsound() {
    let clean = whole_mathlib_class(0, 0);
    let restrictive = whole_mathlib_class(0, 7);
    let unsound = whole_mathlib_class(3, 0);

    // ANTI-VACUITY: three distinct tokens, or the precedence assertions below
    // are satisfiable by a function that returns the same string always.
    assert_eq!(
        [clean, restrictive, unsound]
            .iter()
            .collect::<BTreeSet<_>>()
            .len(),
        3,
        "the three class tokens must differ, or nothing below discriminates"
    );

    // THE CASE THAT WAS NEVER EVALUATED.
    assert_eq!(
        whole_mathlib_class(3, 7),
        unsound,
        "a run that is BOTH unsound and restrictive must be classified by its most severe \
         finding. D23 gives restrictive divergences a repair path and gives an unsound acceptance \
         none, so filing this run as merely restrictive would record the one release-blocking \
         outcome this lane can produce as the ordinary kind"
    );

    // A legal population exhibiting both directions at once.
    let mut counts = CorpusCounts {
        decoded: 700_011,
        compared: 600_011,
        agree: 600_000,
        unsoundly_permissive: 1,
        restrictive_without_carve_out: 10,
        unscorable: 100_000,
        oracle_skipped: 60_000,
        subject_no_answer: 40_000,
        ..CorpusCounts::default()
    };
    counts
        .restrictive_families
        .insert("rejected:BlockMismatch".to_string(), 10);
    counts
        .no_answer_families
        .insert(FAMILY_UNFAITHFUL_IMPORT_CONTEXT.to_string(), 40_000);
    counts.assert_conservation("unsound and restrictive");

    let spec = CorpusReceiptSpec {
        bead: "franken_lean-t6r7",
        corpus_commit: suite_lock_corpus_commit(),
        seed_modules: 8_009,
        receipt_path_var: "FLN_WHOLE_MATHLIB_RECEIPT",
    };
    let receipt = WholeMathlibReceipt::from_run(&WholeMathlibRunFacts {
        spec: &spec,
        counts: &counts,
        closure_modules: 10_007,
        corpus_fixture_hash: "both-directions-at-once",
        observed_unix_s: 1_786_555_666,
        wall_ms: 13,
    });
    assert_eq!(
        receipt.class, unsound,
        "the producer must file the more severe class"
    );
    if let Err(reason) = receipt.validate(&suite_lock_reference_pin(), &suite_lock_corpus_commit())
    {
        panic!("the correctly classified row was refused: {reason}");
    }

    // THE DOWNGRADE MUST BE REFUSED. Rows can be written by hand into the
    // retained file, so the producer choosing correctly is not sufficient.
    for downgraded in [restrictive, clean] {
        let forged = WholeMathlibReceipt {
            class: downgraded.to_string(),
            ..WholeMathlibReceipt::from_run(&WholeMathlibRunFacts {
                spec: &spec,
                counts: &counts,
                closure_modules: 10_007,
                corpus_fixture_hash: "both-directions-at-once",
                observed_unix_s: 1_786_555_666,
                wall_ms: 13,
            })
        };
        let reason = forged
            .validate(&suite_lock_reference_pin(), &suite_lock_corpus_commit())
            .expect_err("a downgraded class must be refused");
        assert!(
            reason.contains(unsound),
            "the refusal must name the class the counts actually earn, so the row can be \
             corrected rather than merely rejected: {reason}"
        );
    }
}

/// The ROUTER and the CENSUS agree about what a token means.
///
/// **A prose join between two functions, made checkable.** `check_family_token`'s
/// direction rule is justified in its own doc comment by how `subject_axis`
/// routes: restrictive families must start with `rejected:` BECAUSE that is
/// exactly the condition on which an outcome becomes `Rejected`. That reasoning
/// is correct today and nothing enforces it. `subject_axis` has one call site,
/// inside the scorer, and no test at all -- so the sentence justifying one rule
/// depends on the untested behaviour of another.
///
/// **What breaks if they drift, and why it is not loud.** Widen `subject_axis` to
/// `contains("rejected")` and an outcome like `inconclusive:rejected_by_peer`
/// becomes a Rejected -- its token would then be counted into
/// `restrictive_families`, where `check_family_token` refuses it, and
/// `assert_conservation` panics thousands of modules into a run with a message
/// about family tokens rather than about routing. Narrow it instead and genuine
/// rejections land in the non-answer census, which is the exact confusion the two
/// maps were split apart to prevent: a kernel divergence reported as an
/// exhaustion, in the D23 direction that matters.
///
/// **The population is production-derived, not hand-listed.** Rejection tokens
/// come from the real `RejectClass` variants and non-answer tokens from the real
/// `resource_usage_facts`, so this checks the strings the lane actually routes.
#[test]
fn the_outcome_router_and_the_family_census_agree_on_direction() {
    let outcome_named = |token: &str| UnitOutcome {
        lead: "Fixture.Decl".to_string(),
        kind: "definition",
        members: 1,
        outcome: token.to_string(),
        message: "detail".to_string(),
        steps_used: 1,
        max_depth: 1,
    };

    let mut tokens = vec!["accepted".to_string(), "internal_fault".to_string()];
    for class in reject_class_variants_from_source() {
        tokens.push(format!("rejected:{class}"));
    }
    for reason in [
        ResourceReason::ExecutionSteps,
        ResourceReason::Cancelled,
        ResourceReason::RecursionDepth { limit: 4 },
    ] {
        tokens.push(
            resource_usage_facts(&ResourceUsage {
                reason,
                allowed: 1,
                observed: 2,
            })
            .0,
        );
    }
    for unit in StructuralUnit::ALL {
        tokens.push(
            resource_usage_facts(&ResourceUsage {
                reason: ResourceReason::StructuralBudget { unit },
                allowed: 1,
                observed: 2,
            })
            .0,
        );
    }

    // ANTI-VACUITY: the population must actually contain all three routings, or
    // the match below checks fewer cases than it appears to.
    let (mut accepted, mut rejected, mut no_answer) = (0_u32, 0_u32, 0_u32);

    for token in &tokens {
        match subject_axis(&outcome_named(token)) {
            CorpusAxisVerdict::Accepted => {
                accepted += 1;
                assert_eq!(token, "accepted");
                // An agreement belongs to NEITHER census. If it were admitted to
                // one, agreements would be counted as findings.
                // Each direction refuses it under a DIFFERENT rule, and saying
                // which is the point: restrictive because it is not a
                // `rejected:` token, non-answer because `accepted` is named
                // explicitly. A bare is_err() pair would hide either one going
                // dark.
                assert_family_token_refused(
                    token,
                    FamilyDirection::Restrictive,
                    "is not a `rejected:` token",
                );
                assert_family_token_refused(
                    token,
                    FamilyDirection::NoAnswer,
                    "is the ACCEPTED token",
                );
            }
            CorpusAxisVerdict::Rejected(_) => {
                rejected += 1;
                if let Err(reason) = check_family_token(token, FamilyDirection::Restrictive) {
                    panic!(
                        "`{token}` is routed to Rejected, so the scorer files it in \
                         `restrictive_families` -- but the census refuses it there: {reason}. The \
                         router and the census disagree about what this token means, and the lane \
                         would panic mid-run about family tokens rather than about routing"
                    );
                }
                assert_family_token_refused(
                    token,
                    FamilyDirection::NoAnswer,
                    "is a `rejected:` token",
                );
            }
            CorpusAxisVerdict::NoAnswer(_) => {
                no_answer += 1;
                if let Err(reason) = check_family_token(token, FamilyDirection::NoAnswer) {
                    panic!(
                        "`{token}` is routed to NoAnswer, so the scorer files it in \
                         `no_answer_families` -- but the census refuses it there: {reason}"
                    );
                }
                // A budget exhaustion counted as a D23 finding would report the
                // kernel as diverging where it only ran out of fuel.
                assert_family_token_refused(
                    token,
                    FamilyDirection::Restrictive,
                    "is not a `rejected:` token",
                );
            }
        }
    }

    assert_eq!(
        accepted, 1,
        "exactly one token should route as an agreement"
    );
    assert!(
        rejected >= 17,
        "every kernel rejection class should have routed as a rejection; {rejected} did"
    );
    assert!(
        no_answer >= 1 + StructuralUnit::ALL.len() as u32,
        "the non-answer routings are missing: {no_answer}"
    );
}

/// A D23 carve-out is PER DECLARATION, and the rule is proved on a planted
/// registry because the real one is empty.
///
/// **The guard that already exists here is vacuous.**
/// `corpus_comparator_preserves_d23_asymmetry_and_no_answer` asserts that every
/// row of `CORPUS_CARVE_OUTS` carries a non-empty justification. `CORPUS_CARVE_OUTS`
/// is `&[]`. `all()` over nothing is true, so that assertion passes no matter what
/// the rule says, and deleting the rule entirely would not redden it. The
/// carve-out branch in the scorer is unreachable for the same reason: the lookup
/// cannot return `Some` when there is nothing to find.
///
/// **Zero is the right population and it is also why nothing is tested.** No
/// carve-out should exist -- the bead's history is emphatic that the 265 were
/// repaired rather than excused -- so the registry must stay empty. But an empty
/// population makes every rule over it unkillable, and the day someone adds the
/// first row, the rules governing it will never have run. A planted registry is
/// the only thing that can carry the check in the meantime.
///
/// **What the plant pins, and why each one matters.** D23 says a carve-out is per
/// declaration with a non-empty Behavior Note. So the lookup must match the whole
/// name and nothing else: if it matched a PREFIX, one row reading `List` would
/// silently excuse every `List.*` divergence in the corpus, and the lane would
/// report carve-outs it never reviewed. Both directions are checked -- a query
/// that extends a planted name, and a planted name that extends the query --
/// because a `starts_with` and a `contains` fail differently and only one of the
/// two probes catches each.
#[test]
fn a_carve_out_matches_one_whole_declaration_name_and_nothing_else() {
    // The REAL registry's rule, restated over the real population. It is
    // vacuous today by design; it becomes load-bearing the moment a row lands.
    assert!(
        CORPUS_CARVE_OUTS
            .iter()
            .all(|row| !row.justification.trim().is_empty() && !row.declaration.trim().is_empty()),
        "every D23 carve-out names a declaration and carries a justification"
    );

    // THE PLANT. Two rows whose names deliberately overlap, so prefix and
    // substring matching are both distinguishable from exact matching.
    const PLANTED: &[CorpusCarveOut] = &[
        CorpusCarveOut {
            declaration: "List.map",
            justification: "planted; this registry is a fixture and governs nothing",
        },
        CorpusCarveOut {
            declaration: "List.mapM",
            justification: "planted; distinguishes exact matching from a prefix match",
        },
    ];

    // Exact hits, each landing on its own row rather than on the first one that
    // shares a prefix.
    assert_eq!(
        carve_out_in(PLANTED, "List.map").map(|row| row.declaration),
        Some("List.map")
    );
    assert_eq!(
        carve_out_in(PLANTED, "List.mapM").map(|row| row.declaration),
        Some("List.mapM"),
        "`List.map` is a prefix of `List.mapM`; a lookup that stopped at the first prefix match \
         would excuse the wrong declaration"
    );

    // CASE ALONE MUST MISS, and this pair is the only thing here that says so.
    // Every miss below differs from a planted name by more than case, so a
    // lookup written with `eq_ignore_ascii_case` returns exactly what `==`
    // returns on all of them and cannot be told apart. Measured over the whole
    // list before these two were added.
    //
    // The harm is not hypothetical in this repository's subject matter: `List`
    // and `list` are both real Lean namespaces -- the lowercase one is the Lean 3
    // spelling -- so a case-blind lookup would let one reviewed row excuse a
    // DIFFERENT declaration, which is precisely what the message below warns
    // about.
    for variant in ["list.map", "LIST.MAP"] {
        assert!(
            PLANTED
                .iter()
                .any(|row| row.declaration.eq_ignore_ascii_case(variant)),
            "`{variant}` must differ from a planted name by CASE ALONE, or it is an ordinary miss \
             and distinguishes nothing"
        );
        assert!(
            !PLANTED.iter().any(|row| row.declaration == variant),
            "`{variant}` must not BE a planted name, or the miss below is asking for a hit"
        );
    }

    // Misses, in both directions.
    for absent in [
        "List",          // a PREFIX of a planted name
        "List.mapM.aux", // EXTENDS a planted name
        "List.mapA",     // shares a prefix, matches neither
        "Array.map",     // unrelated
        "",              // empty
        "list.map",      // differs by CASE alone
        "LIST.MAP",      // and again, the other way
    ] {
        assert!(
            carve_out_in(PLANTED, absent).is_none(),
            "`{absent}` matched a carve-out. D23 excuses ONE declaration per row: a lookup that \
             matched a prefix or a substring would let a single reviewed row silently excuse \
             every declaration sharing its name, and the lane would report carve-outs nobody \
             reviewed"
        );
    }

    // The justification rule, made killable by a row that violates it -- the
    // thing the real registry cannot supply.
    const UNJUSTIFIED: &[CorpusCarveOut] = &[CorpusCarveOut {
        declaration: "List.map",
        justification: "   ",
    }];
    assert!(
        UNJUSTIFIED
            .iter()
            .any(|row| row.justification.trim().is_empty()),
        "the planted violation must actually violate the rule, or the check above it is still \
         vacuous"
    );
}

/// The PUBLISHED disagreement count is the sum of the three D23 buckets, and
/// every one of them is in it.
///
/// **This is the number that gets quoted, and nothing checked it.**
/// `CorpusCounts::disagreements` has exactly two call sites and BOTH are inside
/// `println!`: the per-module `kernel_reference_corpus module=... disagreements=`
/// row and the `SUMMARY` line. No assertion anywhere reads it. The terminal
/// assertions at the end of the driver check `unsoundly_permissive` and
/// `restrictive_without_carve_out` DIRECTLY, so a term dropped from this sum
/// changes what the lane REPORTS while leaving everything the lane ENFORCES
/// intact.
///
/// That is the worst shape a reporting bug can have here. Every figure in this
/// bead's history -- the original 265, the 93, the 1,482 -- came off these two
/// lines. A `disagreements()` missing `restrictive_without_carve_out` would have
/// published "0 disagreements" for a run that found hundreds, and the run would
/// still have failed its assertions for the right reason with the wrong headline
/// in the log.
///
/// **Each term is checked by sensitivity, not by re-adding them up.** Re-deriving
/// the same sum in the test would restate the implementation and agree with any
/// version of it. Instead each bucket is zeroed in turn and the published number
/// must fall by exactly that bucket's amount, which proves the term is present
/// with coefficient one. The three buckets carry DISTINCT values so a drop cannot
/// be mistaken for a different drop.
///
/// **The probes are deliberately not legal populations.** Zeroing one bucket
/// breaks `compared == agree + buckets`, so `assert_conservation` is run on the
/// baseline only; the variants exist to interrogate the arithmetic, not to model
/// a run.
#[test]
fn the_published_disagreement_count_includes_every_d23_bucket() {
    let library = write_inventory_fixture(
        "t6r7-disagreement-v1",
        &["One.olean", "Two.olean", "Three.olean"],
    );
    let seen = walk_olean_inventory(&library, Some("D"))
        .unwrap_or_else(|reason| panic!("walk the fixture: {reason}"))
        .modules
        .len() as u64;
    assert_eq!(seen, 3);

    // Distinct per bucket, so dropping any one is distinguishable from dropping
    // another rather than merely from dropping nothing.
    let (permissive, with_carve_out, without_carve_out) = (1_u64, 2_u64, seen);
    let baseline = || {
        let mut counts = CorpusCounts {
            decoded: 20,
            compared: 16,
            agree: 10,
            unsoundly_permissive: permissive,
            restrictive_with_carve_out: with_carve_out,
            restrictive_without_carve_out: without_carve_out,
            unscorable: 4,
            oracle_skipped: 1,
            subject_no_answer: 3,
            ..CorpusCounts::default()
        };
        counts
            .restrictive_families
            .insert("rejected:BlockMismatch".to_string(), 2);
        counts
            .restrictive_families
            .insert("rejected:TypeMismatch".to_string(), 3);
        counts
            .no_answer_families
            .insert("inconclusive:Steps".to_string(), 3);
        counts
    };
    let counts = baseline();
    counts.assert_conservation("published disagreements");

    let published = counts.disagreements();
    assert_eq!(
        published,
        permissive + with_carve_out + without_carve_out,
        "the published count must be the sum of the three D23 buckets"
    );
    // The identity the SUMMARY line implicitly claims when it prints `compared`,
    // the buckets and this number side by side.
    assert_eq!(
        counts.compared,
        counts.agree + published,
        "every compared declaration either agreed or disagreed; the row cannot print a `compared` \
         that its own parts do not reconstruct"
    );

    // SENSITIVITY, one bucket at a time.
    for (name, dropped, mutate) in [
        (
            "unsoundly_permissive",
            permissive,
            (|c: &mut CorpusCounts| c.unsoundly_permissive = 0) as fn(&mut CorpusCounts),
        ),
        ("restrictive_with_carve_out", with_carve_out, |c| {
            c.restrictive_with_carve_out = 0
        }),
        ("restrictive_without_carve_out", without_carve_out, |c| {
            c.restrictive_without_carve_out = 0
        }),
    ] {
        let mut probe = baseline();
        mutate(&mut probe);
        assert_eq!(
            probe.disagreements(),
            published - dropped,
            "zeroing `{name}` changed the published disagreement count by something other than \
             {dropped}, so that bucket is not in the sum with coefficient one. A term missing \
             here under-reports divergences in the one number this lane publishes, while every \
             assertion the lane enforces keeps passing"
        );
    }

    // And nothing that is NOT a disagreement may leak into it.
    for (name, mutate) in [
        (
            "agree",
            (|c: &mut CorpusCounts| c.agree += 97) as fn(&mut CorpusCounts),
        ),
        ("unscorable", |c: &mut CorpusCounts| c.unscorable += 97),
        ("oracle_skipped", |c: &mut CorpusCounts| {
            c.oracle_skipped += 97
        }),
        ("subject_no_answer", |c: &mut CorpusCounts| {
            c.subject_no_answer += 97
        }),
    ] {
        let mut probe = baseline();
        mutate(&mut probe);
        assert_eq!(
            probe.disagreements(),
            published,
            "`{name}` moved the published disagreement count. A non-answer or an agreement \
             counted as a divergence would report the kernel as differing from the Reference \
             where it did not"
        );
    }
}

/// Run `assert_conservation` over a deliberately illegal population and return
/// the law it broke.
///
/// The panic hook is silenced around the call so a planted violation does not
/// read as a failure in the log, and restored immediately after.
fn conservation_violation(counts: &CorpusCounts) -> String {
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        counts.assert_conservation("planted violation")
    }));
    std::panic::set_hook(previous);
    let payload = outcome.expect_err("an illegal population must not conserve");
    payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| {
            payload
                .downcast_ref::<&str>()
                .map(|text| (*text).to_string())
        })
        .unwrap_or_default()
}

/// Each of the five conservation laws catches its OWN violation.
///
/// **Six live laws, zero demonstrations.** Five arithmetic, plus the family-token
/// rule the loop applies before them. `assert_conservation` runs on every
/// scored module and on the corpus total, and every test that calls it hands it
/// a LEGAL population -- so it has never once fired. Delete any single law and
/// nothing on this bead would notice: the scorer would go on producing legal
/// counts, and the remaining laws would go on passing. That is the same shape as
/// the empty carve-out registry and the collision detector that never collided,
/// in the code that protects the corpus census itself.
///
/// **Each cell breaks exactly one field of a legal base.** Starting from a
/// population that satisfies all six and changing one number is what makes the
/// resulting message attributable; a probe that violated two laws would be
/// caught by whichever is checked first and would say nothing about the other.
///
/// **The expectations name the part that differs.** Two of the six messages end
/// `must be triaged to exactly one family`, so a cell asserting on that phrase
/// would pass for either. The restrictive and non-answer cells assert on
/// `restrictive row` and `subject non-answer` instead.
#[test]
fn each_conservation_law_catches_its_own_violation() {
    let legal = || {
        let mut counts = CorpusCounts {
            decoded: 10,
            compared: 6,
            agree: 4,
            unsoundly_permissive: 1,
            restrictive_without_carve_out: 1,
            unscorable: 4,
            oracle_skipped: 3,
            subject_no_answer: 1,
            ..CorpusCounts::default()
        };
        counts
            .restrictive_families
            .insert("rejected:BlockMismatch".to_string(), 1);
        counts
            .no_answer_families
            .insert("inconclusive:Steps".to_string(), 1);
        counts
    };
    // THE BASE MUST BE LEGAL, or every probe below fires for the wrong law.
    legal().assert_conservation("legal base");

    // EACH SUM LAW IS BROKEN IN ONLY ONE DIRECTION BELOW, so a one-sided
    // comparison survives. Measured, per law, against the legal base and both
    // directions: `decoded = 11` is refused by `<=` as well as by `==`, so `<=`
    // stands in for the law; `agree = 5` is refused by `>=`; `oracle_skipped = 2`
    // is refused by `<=`. The three MIRROR cases at the end of this list are the
    // inputs that kill each of those, and the legal base is accepted by all
    // three variants, so they are not merely "everything refuses".
    //
    // The direction matters for what the law means. A rule that only catches
    // over-counting lets the census credit work it never did: `decoded` below
    // `compared + unscorable` says rows were scored without being decoded, and
    // buckets below `compared` says a compared row landed in no direction at
    // all.
    let cases: [(&str, fn(&mut CorpusCounts), &str); 9] = [
        (
            // The token loop runs BEFORE the sum checks, so this must keep the
            // family SUM correct: otherwise the restrictive-triage law would
            // fire instead and this cell would prove nothing about tokens.
            "a restrictive family is not a rejection token",
            |counts| {
                counts.restrictive_families.clear();
                counts
                    .restrictive_families
                    .insert("inconclusive:Steps".to_string(), 1);
            },
            "is not a `rejected:` token",
        ),
        (
            "decoded no longer covers compared plus unscorable",
            |counts| counts.decoded = 11,
            "decoded must equal compared + unscorable",
        ),
        (
            "a compared row belongs to no direction bucket",
            |counts| counts.agree = 5,
            "D23 direction buckets",
        ),
        (
            "an unscorable row is neither an oracle skip nor a subject non-answer",
            |counts| counts.oracle_skipped = 2,
            "unscorable rows must split",
        ),
        (
            "a restrictive row is triaged to no family",
            |counts| counts.restrictive_families.clear(),
            "every restrictive row",
        ),
        (
            "a non-answer is triaged twice",
            |counts| {
                counts
                    .no_answer_families
                    .insert("inconclusive:Steps".to_string(), 2);
            },
            "every subject non-answer",
        ),
        (
            // MIRROR of the decoded law: fewer decoded than were scored.
            "decoded falls BELOW compared plus unscorable",
            |counts| counts.decoded = 9,
            "decoded must equal compared + unscorable",
        ),
        (
            // MIRROR of the direction law: a compared row in no bucket at all.
            "the direction buckets fall BELOW compared",
            |counts| counts.agree = 3,
            "D23 direction buckets",
        ),
        (
            // MIRROR of the unscorable split: the parts exceed the whole.
            "the unscorable parts EXCEED unscorable",
            |counts| counts.oracle_skipped = 4,
            "unscorable rows must split",
        ),
    ];

    let mut seen: Vec<String> = Vec::new();
    for (name, break_one_law, expected) in cases {
        let mut counts = legal();
        break_one_law(&mut counts);
        let message = conservation_violation(&counts);
        assert!(
            message.contains(expected),
            "`{name}` broke a law, but not the one it names: expected `{expected}`, got \
             `{message}`"
        );
        seen.push(message);
    }

    // NO TWO CELLS MAY HAVE TRIPPED THE SAME LAW. Distinct violations must
    // produce distinct complaints, or one law is standing in for another and the
    // cell that appears to cover it covers nothing. The mirrors pass this
    // because each complaint is an `assert_eq!` panic carrying its two values:
    // `left: 9` and `left: 11` are different messages about the same law, which
    // is exactly what a mirror is.
    for (index, message) in seen.iter().enumerate() {
        for (other, other_message) in seen.iter().enumerate() {
            assert!(
                index == other || message != other_message,
                "two planted violations produced the same complaint: {message}"
            );
        }
    }
}

/// Per-module counts ACCUMULATE into a corpus total, families included.
///
/// **The one production function on this path with no coverage at all.**
/// `CorpusCounts::add` has exactly one call site -- inside the corpus driver,
/// which needs a corpus this host does not have -- so the family merge has never
/// executed anywhere. Every other test on this bead builds a `CorpusCounts`
/// directly and asserts over it; none of them ever adds two together, which is
/// what the lane does once per module for thousands of modules.
///
/// **Its failure modes are all quiet at the point of the mistake.** `insert`
/// instead of `+=` would make a shared family's total equal the LAST module's
/// count rather than the sum. Merging `restrictive_families` and forgetting
/// `no_answer_families` -- two near-identical loops, easy to write once -- would
/// drop most of the corpus's non-answers. Both would be caught eventually by
/// `assert_conservation` on the total, but only at corpus scale, hours into a run
/// nobody can currently perform, and reported as a conservation violation rather
/// than as an accumulator bug.
///
/// **The two populations are shaped to discriminate.** They SHARE one family, so
/// an overwriting merge produces a visibly wrong number rather than a plausible
/// one; and each carries a family the other lacks, so a merge that dropped either
/// side loses something nameable. Both conditions are asserted before the merge
/// is checked, because a merge tested on disjoint or identical censuses proves
/// almost nothing.
#[test]
fn per_module_counts_accumulate_into_a_total_including_their_families() {
    // The sizes come off two real trees, so the totals below are the sum of two
    // things that were actually walked rather than two numbers chosen to add up.
    let first_library =
        write_inventory_fixture("t6r7-accumulate-a-v1", &["One.olean", "Two.olean"]);
    let second_library = write_inventory_fixture(
        "t6r7-accumulate-b-v1",
        &["Alpha.olean", "Beta/Gamma.olean", "Delta.olean"],
    );
    let first_walk = walk_olean_inventory(&first_library, Some("A"))
        .unwrap_or_else(|reason| panic!("walk the first fixture: {reason}"));
    let second_walk = walk_olean_inventory(&second_library, Some("B"))
        .unwrap_or_else(|reason| panic!("walk the second fixture: {reason}"));
    let (first_seen, second_seen) = (
        first_walk.modules.len() as u64,
        second_walk.modules.len() as u64,
    );
    assert_eq!((first_seen, second_seen), (2, 3));

    // A module whose import context could not be rebuilt: everything decoded,
    // nothing compared, every row a non-answer under one family.
    let mut first = CorpusCounts {
        decoded: first_seen,
        unscorable: first_seen,
        subject_no_answer: first_seen,
        ..CorpusCounts::default()
    };
    first
        .no_answer_families
        .insert(FAMILY_UNFAITHFUL_IMPORT_CONTEXT.to_string(), first_seen);
    first.assert_conservation("first module");

    // A module that was partly compared, found one restrictive divergence, and
    // could not answer for the rest.
    let mut second = CorpusCounts {
        decoded: second_seen,
        compared: 1,
        restrictive_without_carve_out: 1,
        unscorable: 2,
        subject_no_answer: 2,
        ..CorpusCounts::default()
    };
    second
        .restrictive_families
        .insert("rejected:BlockMismatch".to_string(), 1);
    second
        .no_answer_families
        .insert(FAMILY_UNFAITHFUL_IMPORT_CONTEXT.to_string(), 1);
    second
        .no_answer_families
        .insert("inconclusive:Steps".to_string(), 1);
    second.assert_conservation("second module");

    // ANTI-VACUITY on the merge's inputs, before the merge is checked.
    assert!(
        first
            .no_answer_families
            .contains_key(FAMILY_UNFAITHFUL_IMPORT_CONTEXT)
            && second
                .no_answer_families
                .contains_key(FAMILY_UNFAITHFUL_IMPORT_CONTEXT),
        "the two censuses must SHARE a family, or an overwriting merge is indistinguishable from \
         a summing one"
    );
    assert!(
        !second.no_answer_families.is_empty()
            && second
                .no_answer_families
                .keys()
                .any(|family| !first.no_answer_families.contains_key(family)),
        "the second census must carry a family the first lacks, or a merge that dropped one side \
         would still look complete"
    );
    assert!(
        first.restrictive_families.is_empty() && !second.restrictive_families.is_empty(),
        "exactly one side must carry a restrictive family, so a dropped merge is nameable"
    );

    let mut total = CorpusCounts::default();
    total.add(&first);
    total.add(&second);

    assert_eq!(total.decoded, first_seen + second_seen);
    assert_eq!(total.compared, 1);
    assert_eq!(total.restrictive_without_carve_out, 1);
    assert_eq!(total.subject_no_answer, first_seen + 2);

    // THE SHARED FAMILY SUMS. Overwriting would leave 1 here, dropping the
    // second side would leave 2, and both are plausible-looking numbers.
    assert_eq!(
        total
            .no_answer_families
            .get(FAMILY_UNFAITHFUL_IMPORT_CONTEXT)
            .copied(),
        Some(first_seen + 1),
        "the family both modules reported must be the SUM of what each reported: {:?}",
        total.no_answer_families
    );
    // The families only one side reported must survive the merge.
    assert_eq!(
        total.no_answer_families.get("inconclusive:Steps").copied(),
        Some(1)
    );
    assert_eq!(
        total
            .restrictive_families
            .get("rejected:BlockMismatch")
            .copied(),
        Some(1)
    );
    assert_eq!(
        total.no_answer_families.len(),
        2,
        "the merged census gained or lost a family: {:?}",
        total.no_answer_families
    );

    // The live law over the accumulated population, which is the thing the lane
    // actually asserts once per module and once over the corpus.
    total.assert_conservation("accumulated corpus");
}

/// The census is CANONICAL: two runs that saw the same families produce
/// byte-identical rows, whatever order the families were first seen in.
///
/// **A vacuity in my own earlier test is what prompted this.**
/// `the_receipt_producer_maps_every_count_to_its_own_field` asserts the census
/// comes out as an exact sorted vector -- but it INSERTS `rejected:BlockMismatch`
/// before `rejected:TypeMismatch`, and `context:...` before `inconclusive:...`.
/// Both censuses are therefore inserted in the order they are expected to emerge,
/// so that assertion passes identically whether the emitter sorts, preserves
/// insertion order, or does anything else that happens to agree on an
/// already-ordered input. It cannot fail for the reason it appears to check.
///
/// **What the property is actually for.** `to_row` is a CANONICAL form, and
/// `from_row` refuses any row it cannot re-serialize byte for byte. If the census
/// order depended on the order families were encountered -- which is the order the
/// corpus happens to be walked in -- then two runs over the same corpus could
/// emit different bytes for the same observation, and a retained row from one
/// would be refused as non-canonical when read by the other. That failure would
/// be intermittent and would look like file corruption rather than like an
/// ordering bug.
///
/// **The mutant this is aimed at is one word.** `BTreeMap` guarantees the order;
/// `HashMap` would not, and swapping them is a plausible edit that nothing else
/// here would catch. So the fixture inserts in DELIBERATELY reversed order and
/// asserts both that the output is sorted and that the insertion order was not
/// already the sorted one -- otherwise this test would inherit the same vacuity
/// it exists to remove.
#[test]
fn the_family_census_is_canonical_whatever_order_families_were_seen_in() {
    // Reverse-sorted on purpose. If these are ever re-ordered into sorted order,
    // the anti-vacuity assertion below fails rather than the test silently
    // becoming another copy of the one it repairs.
    let restrictive = [
        ("rejected:TypeMismatch", 5_u64),
        ("rejected:BlockMismatch", 3),
        ("rejected:AlreadyDeclared", 2),
    ];
    let no_answer = [
        ("inconclusive:Steps", 40_u64),
        (
            "context:import_context_not_faithfully_representable",
            40_000,
        ),
    ];
    let mut sorted_restrictive = restrictive.map(|(name, _)| name).to_vec();
    sorted_restrictive.sort_unstable();
    assert_ne!(
        restrictive.map(|(name, _)| name).to_vec(),
        sorted_restrictive,
        "the fixture must be inserted OUT of sorted order, or this test cannot tell a sorting \
         emitter from one that preserves insertion order -- which is exactly the hole it exists \
         to close"
    );

    let build = |forward: bool| {
        let mut counts = CorpusCounts {
            decoded: 700_050,
            compared: 600_010,
            agree: 600_000,
            restrictive_without_carve_out: 10,
            unscorable: 100_040,
            oracle_skipped: 60_000,
            subject_no_answer: 40_040,
            ..CorpusCounts::default()
        };
        // Same content, opposite encounter orders.
        let mut restrictive = restrictive.to_vec();
        let mut no_answer = no_answer.to_vec();
        if !forward {
            restrictive.reverse();
            no_answer.reverse();
        }
        for (name, count) in restrictive {
            counts.restrictive_families.insert(name.to_string(), count);
        }
        for (name, count) in no_answer {
            counts.no_answer_families.insert(name.to_string(), count);
        }
        counts.assert_conservation("canonical census");
        counts
    };

    let first = build(true);
    let second = build(false);

    let rows = family_census_rows(&first.restrictive_families);
    assert_eq!(
        rows,
        vec![
            "rejected:AlreadyDeclared=2".to_string(),
            "rejected:BlockMismatch=3".to_string(),
            "rejected:TypeMismatch=5".to_string(),
        ],
        "the census must be emitted in sorted order, not in the order the families were seen"
    );
    assert_eq!(
        rows,
        family_census_rows(&second.restrictive_families),
        "the two encounter orders produced different censuses"
    );

    // The whole row, which is what actually gets retained and re-read.
    let spec = CorpusReceiptSpec {
        bead: "franken_lean-t6r7",
        corpus_commit: suite_lock_corpus_commit(),
        seed_modules: 8_009,
        receipt_path_var: "FLN_WHOLE_MATHLIB_RECEIPT",
    };
    let receipt_of = |counts: &CorpusCounts| {
        WholeMathlibReceipt::from_run(&WholeMathlibRunFacts {
            spec: &spec,
            counts,
            closure_modules: 10_007,
            corpus_fixture_hash: "same-corpus-either-way",
            observed_unix_s: 1_786_444_555,
            wall_ms: 9,
        })
    };
    let row = receipt_of(&first).to_row();
    assert_eq!(
        row,
        receipt_of(&second).to_row(),
        "two runs over the same corpus emitted different BYTES for the same observation. \
         `from_row` refuses anything it cannot re-serialize exactly, so a row retained by one \
         run would be rejected as non-canonical when read back by the other, intermittently, \
         and it would read as file corruption rather than as an ordering bug"
    );

    // And the canonical row must still be one the guard accepts, from either
    // order: a form nothing can validate is not a canonical form.
    for counts in [&first, &second] {
        if let Err(reason) =
            receipt_of(counts).validate(&suite_lock_reference_pin(), &suite_lock_corpus_commit())
        {
            panic!("a canonical row was refused by its own guard: {reason}");
        }
    }
}

/// Every NON-ANSWER token the lane can actually produce is a legal family too,
/// including the one that is COMPOSED out of another enum.
///
/// **The half of the token law that was never closed.**
/// `every_kernel_rejection_class_yields_a_legal_family_token` walks all 17
/// `RejectClass` variants and the two `context:` reasons. It says nothing about
/// the `inconclusive:` family, which is the other side of the census and the
/// side whose tokens are not constants: `resource_usage_facts` builds
/// `inconclusive:StructuralBudget:<unit>` by interpolating a second enum's name
/// into the token.
///
/// **That composition is exactly what the delimiter rule exists for.** A family
/// token is serialized as `token=count` and joined with `,`. Every other token in
/// the system is a fixed identifier, so the rule looks like paranoia -- but this
/// one's tail comes from `StructuralUnit`, and the day a unit is added whose
/// evidence name carries a comma or an equals sign, every census row containing
/// that family is re-read as different families with different counts, silently.
/// The rule was written for this case and had never been pointed at it.
///
/// **The tokens come from the production function, not from a re-derivation.**
/// `resource_usage_facts` is what the lane calls, so what is checked is the
/// string the lane would actually write. A test that rebuilt the token from its
/// parts would agree with itself and prove nothing. The `match` is exhaustive
/// with no wildcard, so a new `ResourceReason` stops the build here, and the
/// structural units come from `StructuralUnit::ALL` rather than a hand-list.
///
/// **What this does NOT enumerate, said plainly so the count above is not read
/// as the whole population.** `verdict_facts` also emits
/// `inconclusive:Cancelled`, `inconclusive:DependencyUnavailable` and
/// `inconclusive:AuthorityIncomplete` from `InconclusiveCause`. Those three are
/// fixed identifiers with no interpolated tail, so they cannot acquire a
/// delimiter the way the composed token can, and they are not built here. The
/// compile-time completeness this test buys is over `ResourceReason` and
/// `StructuralUnit` only.
#[test]
fn every_non_answer_outcome_yields_a_legal_family_token() {
    let mut tokens = Vec::new();
    for reason in [
        ResourceReason::Heartbeats {
            consumed: 3,
            limit: 2,
        },
        ResourceReason::ExecutionSteps,
        ResourceReason::RecursionDepth { limit: 7 },
        ResourceReason::Cancelled,
        ResourceReason::Memory { limit_bytes: 11 },
    ] {
        // COMPILE-TIME COMPLETENESS: no wildcard, so a new variant is a build
        // error here rather than an untested family token.
        match reason {
            ResourceReason::Heartbeats { .. }
            | ResourceReason::ExecutionSteps
            | ResourceReason::RecursionDepth { .. }
            | ResourceReason::Cancelled
            | ResourceReason::Memory { .. }
            | ResourceReason::StructuralBudget { .. } => {}
        }
        let usage = ResourceUsage {
            reason,
            allowed: 64,
            observed: 65,
        };
        tokens.push(resource_usage_facts(&usage).0);
    }
    // The composed family, over the registered units rather than a hand-list.
    assert!(
        !StructuralUnit::ALL.is_empty(),
        "an empty unit registry would make the composed family vacuous"
    );
    for unit in StructuralUnit::ALL {
        let usage = ResourceUsage {
            reason: ResourceReason::StructuralBudget { unit },
            allowed: 64,
            observed: 65,
        };
        tokens.push(resource_usage_facts(&usage).0);
    }
    // The two remaining non-answer shapes the replay can record.
    tokens.push("internal_fault".to_string());

    assert_eq!(
        tokens.len(),
        6 + StructuralUnit::ALL.len(),
        "the resource-derived non-answer population changed size without this test noticing"
    );

    for token in &tokens {
        if let Err(reason) = check_family_token(token, FamilyDirection::NoAnswer) {
            panic!(
                "the lane can record `{token}` as a non-answer, but the census would refuse it: \
                 {reason}"
            );
        }
        assert_family_token_refused(
            token,
            FamilyDirection::Restrictive,
            "is not a `rejected:` token",
        );
    }

    // The composed token really is composed -- if this stops holding, the case
    // this test exists for has quietly disappeared and the rest is a formality.
    assert!(
        tokens.iter().any(|token| token.matches(':').count() >= 2),
        "no token carries a composed tail any more, so the delimiter rule is no longer being \
         exercised against interpolated content: {tokens:?}"
    );
}

/// The projection refuses a path it cannot honestly name, and each refusal is
/// told apart by the part that DIFFERS.
///
/// **Why these branches are reachable at all.** Called through the walk,
/// `module_name_from_path` only ever sees paths `collect_present_oleans` found
/// beneath the root, so its guards look unreachable like the two in
/// `walk_olean_inventory`. They are not: the function is `pub` within this file
/// and is called DIRECTLY by
/// `the_inventory_vectors_are_parallel_and_the_extension_match_is_exact`, which
/// recomputes each expected name from its own path. A direct caller can hand it
/// anything, and a future one will.
///
/// **What each refusal protects.** A path outside the root would yield a module
/// name for a file the corpus does not contain. A `..` component would yield a
/// name that reads as ordinary while pointing above the tree being inventoried.
/// That one gets two paths as well: one whose `..` is its first component, which
/// any check refuses, and one that begins with an ordinary name and climbs
/// afterwards, which only a check over EVERY component refuses -- the second
/// would otherwise be named `A.up.Thing`.
/// A root with nothing below it would yield the empty name, which would collide
/// with any other empty name and take the injectivity rule down with it. All
/// three produce a plausible-looking module name rather than an error, which is
/// why they are refusals rather than debug assertions.
///
/// **The outside-the-root case gets two paths, because one of them cannot
/// distinguish the rule from its cheap version.** A wholly foreign path is
/// refused by any prefix test. A SIBLING whose directory name extends the
/// root's -- `/corpus/libextra` against `/corpus/lib` -- is refused only by a
/// component-wise one. Without the second, a projection written with
/// `str::starts_with` passes this test while minting `extra.Thing` for a file in
/// a neighbouring library.
///
/// **The expectations are chosen for what separates them.** Counted over the
/// fragments in `MESSAGES` below: three share `module path`, two share `module
/// path component in`, two share `empty module`, and two share `module name` --
/// so asserting on any of those would let one branch pass in another's place.
/// Each cell below asserts on the words unique to its own branch. (This
/// paragraph used to open "four of these five messages share `module path`",
/// which is a miscount: only three of them contain that phrase. A prose tally
/// beside a checked list is the half nobody re-derives.)
#[test]
fn the_module_projection_refuses_a_path_it_cannot_honestly_name() {
    let root = Path::new("/corpus/lib");

    // OUTSIDE THE ROOT. `strip_prefix` is lexical, so this is a real caller
    // error rather than a filesystem question.
    let reason = module_name_from_path(root, Path::new("/elsewhere/Thing.olean"))
        .expect_err("a path outside the root cannot be named against it");
    assert!(
        reason.contains("is outside"),
        "the refusal must say the path is not under the root: {reason}"
    );

    // OUTSIDE THE ROOT BY A PATH TEST, INSIDE IT BY A STRING TEST. The decoy
    // above shares no leading text with the root, so a projection written with
    // `to_str().starts_with(root)` -- the classic wrong way to strip a prefix --
    // refuses it exactly as `strip_prefix` does and cannot be told apart. A
    // SIBLING whose name extends the root's can: `/corpus/libextra` starts with
    // `/corpus/lib` as text and is not below it as a path.
    //
    // What the string version would mint is the point. Measured: it strips the
    // root's characters, leaving `extra/Thing.olean`, and names the module
    // `extra.Thing` -- a module named after a fragment of a neighbouring
    // directory's name, which resolves against no import and belongs to no
    // library.
    const SIBLING: &str = "/corpus/libextra/Thing.olean";
    assert!(
        SIBLING.starts_with(root.to_str().unwrap_or_default()),
        "the sibling must match the root as TEXT, or it does not distinguish a string prefix from \
         a path prefix"
    );
    assert!(
        !"/elsewhere/Thing.olean".starts_with(root.to_str().unwrap_or_default()),
        "the decoy above must NOT match as text; that is why it cannot tell the two apart"
    );
    let sibling = module_name_from_path(root, Path::new(SIBLING))
        .expect_err("a sibling whose name merely extends the root's is not below it");
    assert!(
        sibling.contains("is outside"),
        "the sibling must be refused for being outside the root, like any other foreign path: \
         {sibling}"
    );

    // A NON-NORMAL COMPONENT. `strip_prefix` keeps `..` verbatim, so the
    // relative path escapes upward while still looking like a module path.
    let reason = module_name_from_path(root, Path::new("/corpus/lib/../up/Thing.olean"))
        .expect_err("a `..` component cannot be projected to a module name");
    assert!(
        reason.contains("non-normal"),
        "`non-normal` is the only word separating this from the empty-component \
         refusal, which shares `module path component in`: {reason}"
    );

    // A NON-NORMAL COMPONENT THAT IS NOT THE FIRST ONE. The relative path above
    // begins with `..`, so a check written as "is the first component ordinary"
    // -- looking at where the path starts rather than at what it contains --
    // refuses it exactly as a check over every component does. The path below
    // starts with an ordinary name and climbs afterwards.
    //
    // What the first-component version would mint is the point, and it was
    // measured: it keeps the Normal components and drops the rest, naming the
    // module `A.up.Thing` -- a name claiming `up` sits under `A`, for a file that
    // actually resolves to `/corpus/up`. Plausible, wrong, and attached to the
    // wrong library.
    const DEEP: &str = "/corpus/lib/A/../../up/Thing.olean";
    let deep_relative = Path::new(DEEP)
        .strip_prefix(root)
        .expect("the path is lexically below the root; that is why the component check matters");
    assert!(
        matches!(
            deep_relative.components().next(),
            Some(std::path::Component::Normal(_))
        ),
        "the relative path must START with an ordinary component, or a first-component check \
         refuses it too and this cell distinguishes nothing"
    );
    assert!(
        deep_relative
            .components()
            .any(|component| !matches!(component, std::path::Component::Normal(_))),
        "and it must still climb somewhere, or there is nothing to refuse"
    );
    let shallow_relative = Path::new("/corpus/lib/../up/Thing.olean")
        .strip_prefix(root)
        .expect("the decoy is lexically below the root too");
    assert!(
        !matches!(
            shallow_relative.components().next(),
            Some(std::path::Component::Normal(_))
        ),
        "the decoy above must begin with the offending component; that is why it cannot tell a \
         first-component check from a whole-path one"
    );
    let deep = module_name_from_path(root, Path::new(DEEP))
        .expect_err("a `..` anywhere in the relative path cannot be projected");
    assert!(
        deep.contains("non-normal"),
        "climbing from the middle must be refused by the same rule as climbing from the start: \
         {deep}"
    );

    // NOTHING BELOW THE ROOT AT ALL: the relative path is empty, so there are no
    // components to join and the name would be the empty string.
    let reason = module_name_from_path(root, root).expect_err("the root itself names no module");
    assert!(
        reason.contains("empty module name"),
        "`empty module name` is what separates this from the empty-COMPONENT \
         refusal, which also begins `empty module`: {reason}"
    );

    // ANTI-VACUITY on the choice of expectations: each must appear in exactly
    // one of the five messages this function can produce, or a cell could pass
    // on a sibling's refusal. The list is the messages themselves, so it cannot
    // drift from them silently.
    const MESSAGES: [&str; 6] = [
        "is outside",
        "non-normal module path component in",
        "non-UTF-8 module path",
        "empty module path component in",
        "empty module name for",
        "projects to a module name with an empty segment",
    ];
    for probe in [
        "is outside",
        "non-normal",
        "empty module name",
        "empty segment",
    ] {
        assert_eq!(
            MESSAGES.iter().filter(|m| m.contains(probe)).count(),
            1,
            "`{probe}` no longer identifies exactly one refusal of this projection"
        );
    }
    // And the fragments deliberately NOT used, so the reason they were rejected
    // stays visible rather than becoming folklore.
    for shared in ["module path", "empty module"] {
        assert!(
            MESSAGES.iter().filter(|m| m.contains(shared)).count() > 1,
            "`{shared}` is no longer ambiguous; the cells above could be simplified"
        );
    }
}

/// Qualification prepends UNCONDITIONALLY -- the premise that makes the walk's
/// prefix guard unreachable from any tree.
///
/// **Why this is not the existing two-example test.**
/// `mathlib_olean_paths_are_qualified_before_import_matching` already checks
/// `qualify_module_name` on one `Some` and one `None` input. Two examples do not
/// establish the INVARIANT the walk leans on, which is that *every* name comes
/// back carrying the prefix -- and it is the invariant, not the examples, that
/// makes the prefix branch in `walk_olean_inventory` dead code rather than a
/// live check.
///
/// **The case a well-meant repair would break.** A name that already begins with
/// the prefix is qualified again: `Ns.Already` becomes `Ns.Ns.Already`. That
/// looks like a bug and is not one. The projection is mechanical -- filesystem
/// depth to dotted name -- and a module genuinely nested at `Ns/Ns/Already.olean`
/// must produce exactly that. Teaching the qualifier to notice an existing
/// prefix would silently merge two distinct modules into one name, which is the
/// non-injectivity the walk refuses two rules later. So the doubling is pinned
/// deliberately, with the reason attached, rather than left looking like an
/// oversight somebody should tidy.
#[test]
fn qualification_prepends_unconditionally_which_is_why_the_walk_guard_is_defensive() {
    let names = [
        "",
        "Leaf",
        "A.B.C",
        "Ns.Already",
        "Mid.dotted.Leaf",
        "Nsx",
        "ns.lowercase",
    ];
    for name in names {
        let qualified = qualify_module_name(Some("Ns"), name.to_string());
        assert_eq!(
            qualified,
            format!("Ns.{name}"),
            "qualification must be a plain prepend with no special-casing"
        );
        assert!(
            qualified.starts_with("Ns."),
            "`{qualified}` does not carry the prefix, which is the premise the walk's prefix \
             guard is dead because of"
        );
        // The `None` arm hands the name back untouched.
        assert_eq!(qualify_module_name(None, name.to_string()), name);
    }

    // ANTI-VACUITY: the spread must actually contain the awkward shapes, or the
    // loop above is a list of ordinary names dressed up as an invariant.
    assert!(
        names.contains(&"Ns.Already") && names.contains(&"") && names.contains(&"Nsx"),
        "the spread must include an already-prefixed name, an empty one, and one that merely \
         starts with the prefix's letters"
    );
    // `Nsx` shares the prefix's letters but not its dot, so a guard written with
    // `starts_with("Ns")` instead of `starts_with("Ns.")` would accept a name
    // the walk should have rejected.
    assert_eq!(
        qualify_module_name(Some("Ns"), "x".to_string()),
        "Ns.x",
        "the separator is part of the prefix"
    );
}

/// The inventory is SORTED, not merely stable within one process.
///
/// **What the determinism test cannot see.** The receipt-flow test walks one
/// tree twice and requires the two results to agree. That pins stability, and it
/// is exactly the case an UNSORTED walk would also pass: both walks would hit
/// the same `read_dir` in the same process and get the same filesystem order
/// back. The property that actually matters is stronger -- the order must be the
/// same on every machine -- because the fixture hash, the module census and the
/// receipt's counts are all taken from it, and two hosts disagreeing about the
/// order would disagree about the corpus while both looking self-consistent.
///
/// **It rests on three separate `sort` calls** -- one in `walk_olean_inventory`,
/// two inside the helpers it uses -- and nothing asserted any of them.
///
/// **This paragraph used to end "removing any one leaves a walk that is still
/// stable per process and no longer canonical across hosts", and that is false
/// of all three.** Measured, not argued: a depth-first walk whose entries are
/// sorted by file name within each directory emits paths in exactly the order a
/// global sort of those paths produces, because component-wise path order IS
/// lexicographic order on the component sequence. So the innermost sort alone
/// already makes the walk canonical, and either outer sort alone restores the
/// order if the innermost is gone. Each of the three is individually removable
/// with no observable change here, and this test would survive all three
/// single-deletion mutants while its own doc promised they would die.
///
/// The one of the three that CAN be made observable is the innermost, through a
/// caller that does not re-sort;
/// `the_walk_helper_is_canonical_before_any_caller_sorts_it` is that caller. The
/// two outer sorts stay as defence in depth and are declared redundant where
/// they sit, so a mutation campaign records them as known-inert rather than as
/// escaped mutants.
///
/// **The fixture is created in reverse-sorted order on purpose.** On filesystems
/// that hand back entries in creation order -- which is common -- an unsorted
/// walk returns `Zeta` first, so the assertion has something to catch. That the
/// creation order differs from the sorted order is asserted rather than assumed,
/// because a later tidy-up of the file list into alphabetical order would make
/// this test vacuous without changing a single assertion.
#[test]
fn the_inventory_is_sorted_not_merely_stable_within_one_process() {
    const CREATED: [&str; 5] = [
        "Zeta.olean",
        "Mid.olean",
        "Alpha.olean",
        "Nested/Zulu.olean",
        "Nested/Alfa.olean",
    ];
    let library = write_inventory_fixture("t6r7-inventory-sorted-v1", &CREATED);

    let OleanInventory { oleans, modules } = walk_olean_inventory(&library, Some("Fixture"))
        .unwrap_or_else(|reason| panic!("the sorted fixture must be walkable: {reason}"));
    assert_eq!(oleans.len(), CREATED.len());

    // ANTI-VACUITY FIRST: if the list above were already alphabetical, an
    // unsorted walk would satisfy everything below by accident.
    let mut expected_order = CREATED.to_vec();
    expected_order.sort_unstable();
    assert_ne!(
        CREATED.to_vec(),
        expected_order,
        "the fixture must be created OUT of sorted order, or this test cannot tell a sorting \
         walk from one that returns whatever the filesystem hands it"
    );

    assert!(
        oleans.windows(2).all(|pair| pair[0] <= pair[1]),
        "the olean paths came back unsorted, so the inventory's order is whatever this \
         filesystem happened to return: {oleans:?}"
    );
    // THE NAME ORDER IS A COINCIDENCE OF THIS FIXTURE, NOT A PROPERTY OF THE
    // WALK, and asserting it without saying so states something false about the
    // code. `Path` orders COMPONENT BY COMPONENT, so a component that ends sorts
    // before any longer one sharing its bytes: the directory `Algebra` precedes
    // the file `Algebra.olean`, and the child module is enumerated before its
    // parent. The joined name runs past that boundary into a `.` and the next
    // component, so by name the parent comes first. That shape -- a file
    // `X.olean` beside a directory `X/` -- is what a Lean library has wherever a
    // module has submodules, and it is pinned by
    // `a_parent_module_makes_path_order_disagree_with_module_name_order`.
    //
    // No entry here is a parent module, so the two orders coincide, and that
    // premise is asserted rather than assumed: adding `Nested.olean` to the list
    // above would redden the assertion below for a reason that has nothing to do
    // with sorting, and its message would send the reader after the wrong bug.
    assert!(
        !CREATED.iter().any(|entry| {
            entry.strip_suffix(".olean").is_some_and(|stem| {
                let directory = format!("{stem}/");
                CREATED.iter().any(|other| other.starts_with(&directory))
            })
        }),
        "a fixture entry is a parent module -- a file with a directory of the same name beside it \
         -- so path order and module-name order need not agree here and the sortedness check \
         below is no longer the right assertion: {CREATED:?}"
    );
    assert!(
        modules.windows(2).all(|pair| pair[0] <= pair[1]),
        "the module names came back unsorted on a fixture holding no parent module, where path \
         order and name order coincide: {modules:?}"
    );

    // The first file CREATED must not be the first REPORTED -- the single
    // observation that separates a sorted walk from a creation-ordered one on
    // this fixture.
    assert!(
        oleans[0].ends_with("Alpha.olean"),
        "the first reported olean is `{:?}`, but `Alpha.olean` sorts first and `Zeta.olean` was \
         created first; the walk is reporting creation order",
        oleans[0]
    );
}

/// The inventory is ordered by PATH, and a PARENT MODULE makes that differ from
/// module-name order.
///
/// **`Path` orders component by component, not byte by byte.** A component that
/// ends sorts before any longer component sharing its bytes, so the directory
/// `Algebra` precedes the file `Algebra.olean` and the CHILD module is
/// enumerated before its PARENT. The projection then joins components with `.`,
/// and the joined name runs straight past that boundary into the next
/// component's bytes -- so by name `Algebra` precedes `Algebra.Group`. Same
/// tree, opposite orders.
///
/// **This is the ordinary shape of a Lean library, not a contrived tree.**
/// Wherever a module has submodules it is a file `X.olean` sitting beside a
/// directory `X/`, which is exactly the pair above. Neither existing inventory
/// fixture contains one -- the sorted fixture's `Nested/` has no `Nested.olean`,
/// and the parallel fixture's `Mid.dotted/` has no `Mid.dotted.olean` -- which
/// is why nothing in this file has ever observed the disagreement.
///
/// **Which order the walk emits is not a detail.** `modules[i]` has to be the
/// projection of `oleans[i]`, because the struct hands a caller two vectors side
/// by side and
/// `the_inventory_vectors_are_parallel_and_the_extension_match_is_exact` pins
/// that they may be zipped. Path order is what preserves that correspondence, so
/// sorting the NAMES -- the obvious-looking tidy-up -- is the change that would
/// break it. This is the other half of that pin: the price of the
/// correspondence is a module list that is not sorted by name, and a reader who
/// assumes otherwise, with an adjacent dedup, a binary search or a merge against
/// a sorted list, gets a wrong answer on the ordinary library layout rather than
/// on some edge case.
///
/// **The tree is accepted, and every count taken from it is right.** The two
/// names are distinct, so the injectivity rule inside the walk passes; nothing
/// is refused and nothing is counted twice. Only the order is surprising, which
/// is what makes it survivable and therefore worth pinning.
///
/// **This is why the sortedness claim next door had to be split rather than
/// deleted.** `the_inventory_is_sorted_not_merely_stable_within_one_process`
/// asserts the names come back sorted and passes -- truthfully of its fixture,
/// which holds no parent module, and falsely of the walk. That test now states
/// the premise it rests on; this one holds the general case.
#[test]
fn a_parent_module_makes_path_order_disagree_with_module_name_order() {
    let library = write_inventory_fixture(
        "t6r7-inventory-parent-module-v1",
        &["Algebra.olean", "Algebra/Group.olean", "Order.olean"],
    );

    // ANTI-VACUITY, ON THE FIXTURE'S SHAPE. The entire disagreement rests on one
    // name being both a file and a directory. If the writer ever created only
    // one of the two -- or created `Algebra` as a directory alone -- everything
    // below would still run and would be a statement about a pair that is not
    // there.
    assert!(
        library.join("Algebra.olean").is_file(),
        "the parent module file is missing from the fixture, so nothing here is about a parent \
         module"
    );
    assert!(
        library.join("Algebra").is_dir(),
        "the submodule directory is missing from the fixture, so `Algebra.olean` has no child and \
         the orders cannot disagree"
    );

    let OleanInventory { oleans, modules } = walk_olean_inventory(&library, Some("Fixture"))
        .unwrap_or_else(|reason| panic!("a library with a parent module must walk: {reason}"));
    assert_eq!(
        oleans.len(),
        3,
        "the fixture's three files must all be collected before their order means anything: \
         {oleans:?}"
    );

    let index_of = |name: &str| {
        modules
            .iter()
            .position(|module| module == name)
            .unwrap_or_else(|| panic!("`{name}` is not in the inventory: {modules:?}"))
    };
    let parent = index_of("Fixture.Algebra");
    let child = index_of("Fixture.Algebra.Group");

    // THE PATHS ARE SORTED. Without this the rest is a statement about whatever
    // order the filesystem happened to return, not about the projection.
    assert!(
        oleans.windows(2).all(|pair| pair[0] <= pair[1]),
        "the paths came back unsorted, so this test cannot say what path order projects to: \
         {oleans:?}"
    );

    // AND THE CHILD IS REPORTED FIRST, while its name sorts second. Asserted on
    // the one pair that differs rather than as a blanket `windows(2)`, because
    // the other entry is in agreement and would dilute the claim.
    assert!(
        child < parent,
        "`Algebra/Group.olean` must be enumerated before `Algebra.olean` -- the component \
         `Algebra` ends where `Algebra.olean` continues -- or the disagreement this test is \
         about is not present: {oleans:?}"
    );
    assert!(
        modules[child] > modules[parent],
        "the earlier entry `{}` and the later entry `{}` were expected to come back in DESCENDING \
         name order, which is what makes the module list unsorted. If they now ascend, the walk \
         has started ordering by NAME, and the parallel correspondence between `oleans` and \
         `modules` is what to check next",
        modules[child],
        modules[parent]
    );

    // THE CORRESPONDENCE STILL HOLDS ON THIS TREE, which is why the unsorted
    // names are the right answer rather than a bug. Each name is recomputed from
    // its own path by the independent specification, not by the projection under
    // test, so a projection replaced by a stub fails here instead of agreeing
    // with itself.
    for (path, name) in oleans.iter().zip(&modules) {
        assert_eq!(
            name,
            &expected_module_name(&library, path, "Fixture"),
            "`{}` is paired with `{name}`, which is not what its own path means. The two vectors \
             are built by two separate walks and only their lengths are checked, so a change to \
             either one's order silently attributes every module to the wrong file",
            path.display()
        );
    }
}

/// A stem ending in a dot mints a module name no import can ever match, and the
/// guard written for exactly that hazard cannot see it.
///
/// **The guard inspects the path's components; the name is made of segments.**
/// `module_name_from_path` refuses a component that `is_empty()`, which reads
/// like the right rule and is unreachable: a `Component::Normal` produced by the
/// parser is never empty, so that branch cannot fire on any real path. The JOIN
/// is where an empty segment comes from. `x..olean` has extension `olean` and
/// stem `x.`, so `Dotted/x..olean` projected to `Dotted.x.` -- a trailing
/// segment with no characters -- past both guards, because every component along
/// the way was non-empty and normal.
///
/// **The file really does arrive at the projection**, which is the part worth
/// checking rather than assuming: `Path::extension` reports `olean` for
/// `x..olean`, so the walk's exact-extension filter collects it like any other
/// module. The refusal below is therefore about a file the walk hands over, not
/// about one the filter already dropped. That is asserted with the collector
/// itself.
///
/// **What the bad name costs is silence, not a crash.** A name with an empty
/// segment matches no import recorded inside any olean, so the module would join
/// the census, add one to every count taken from it, and resolve against
/// nothing. Downstream that reads as a corpus with unresolved imports -- a
/// corpus-integrity problem -- rather than as a file that should never have been
/// named.
///
/// **Asserted on the part that differs.** `Dotted/..olean` is refused too, but
/// by the NON-NORMAL branch: its stripped form ends in `..`, which
/// `Path::components` reports as `ParentDir`. Two neighbouring dotted names,
/// two different refusals, and a cell that asserted on `refused` alone would
/// pass on either.
#[test]
fn a_stem_ending_in_a_dot_mints_a_name_no_import_can_match() {
    let library = write_inventory_fixture("t6r7-inventory-empty-segment-v1", &["Dotted/x..olean"]);

    // ANTI-VACUITY, BEFORE THE REFUSAL: the walk's extension filter must collect
    // this file. If it did not, the projection would never be handed the path
    // and the refusal below would be a statement about an input that cannot
    // occur.
    let mut collected = Vec::new();
    collect_present_oleans(&library, &mut collected)
        .unwrap_or_else(|reason| panic!("the fixture must enumerate: {reason}"));
    assert_eq!(
        collected.len(),
        1,
        "`x..olean` must reach the projection like any other module -- its extension IS `olean` -- \
         or this test refuses a file the filter already dropped: {collected:?}"
    );

    // Matched rather than `expect_err`, which would need `OleanInventory: Debug`
    // and would print the struct. What matters if this ever succeeds is the
    // NAME it accepted, so the failure says that instead.
    let reason = match walk_olean_inventory(&library, Some("Fixture")) {
        Err(reason) => reason,
        Ok(accepted) => panic!(
            "a tree that cannot be honestly named was counted instead of refused, as {:?}",
            accepted.modules
        ),
    };
    assert!(
        reason.contains("empty segment"),
        "`empty segment` is what separates this from the `empty module path component` refusal \
         and from `empty module name for`, both of which also begin `empty module`: {reason}"
    );
    assert!(
        reason.contains("Dotted.x."),
        "the refusal must show the NAME it would have minted, or the reader has to re-derive the \
         projection to see what was wrong with it: {reason}"
    );

    // THE PART THAT DIFFERS. `..olean` strips to `..`, which is a ParentDir
    // component, so it is refused by the non-normal branch instead. Without this
    // the cell above could be passing on whichever refusal a dotted name happens
    // to hit.
    let root = Path::new("/corpus/lib");
    let parent_dir = module_name_from_path(root, Path::new("/corpus/lib/Dotted/..olean"))
        .expect_err("`..olean` strips to a parent-directory component");
    assert!(
        parent_dir.contains("non-normal") && !parent_dir.contains("empty segment"),
        "`Dotted/..olean` must be refused as NON-NORMAL, not as an empty segment; if both dotted \
         names now take the same branch, one of these cells has stopped testing anything: \
         {parent_dir}"
    );

    // GREEN CONTROL: dots INSIDE a component are ordinary and must still name a
    // module. The new rule is about empty segments, not about dots, and a rule
    // that refused `Mid.dotted` would reject names a Lean library really uses.
    assert_eq!(
        module_name_from_path(root, Path::new("/corpus/lib/Mid.dotted/Leaf.olean"))
            .unwrap_or_else(|reason| panic!("a dotted directory names a module: {reason}")),
        "Mid.dotted.Leaf",
        "a dot inside a component is part of the name, and only a segment with NO characters is \
         refused"
    );
}

/// An empty segment in the MIDDLE of a name, which the trailing decoy cannot
/// distinguish.
///
/// **The neighbouring test's stem puts the empty segment last.**
/// `Dotted/x..olean` projects to `Dotted.x.`, so the cheap version of the rule --
/// "refuse a name that ends in a dot" -- refuses it too, and every assertion
/// there passes for either implementation. One decoy, two rules, nothing between
/// them.
///
/// **`Dotted/a..b.olean` projects to `Dotted.a..b`.** The doubled dot is in the
/// middle, the name does not end in a dot, and only a rule that looks at EVERY
/// segment refuses it. Measured against both rules, with two green names, before
/// this cell was written.
///
/// **Both halves of the input are asserted from the entry itself.** Its stem must
/// still contain a doubled dot -- or it mints no empty segment and the cell tests
/// nothing -- and it must NOT end in one, or the cheap rule refuses it again and
/// the cell quietly becomes a second copy of its neighbour. Both are read off the
/// entry with `Path::file_stem`, not restated as literals.
///
/// **Why an empty segment anywhere is the same defect.** A name with a gap in it
/// matches no import recorded in any olean, whichever end the gap is at. The
/// module joins the census, adds one to every count, and resolves against
/// nothing.
#[test]
fn an_empty_segment_in_the_middle_of_a_name_is_refused_too() {
    const ENTRY: &str = "Dotted/a..b.olean";

    // THE INPUT'S TWO PROPERTIES, READ OFF THE ENTRY. Not asserted as literals:
    // if the fixture list is edited, these are what redden.
    let stem = Path::new(ENTRY)
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or_else(|| panic!("`{ENTRY}` has no usable stem"));
    assert!(
        stem.contains(".."),
        "`{stem}` must run two dots together, or the projection mints no empty segment at all"
    );
    assert!(
        !stem.ends_with('.'),
        "`{stem}` must NOT end in a dot, or a rule that only checks the last segment refuses it \
         too and this cell stops distinguishing anything"
    );

    let library = write_inventory_fixture("t6r7-inventory-empty-segment-mid-v1", &[ENTRY]);

    // ANTI-VACUITY: the file must reach the projection, exactly as in the
    // trailing case. `a..b.olean` has extension `olean` like any other module.
    let mut collected = Vec::new();
    collect_present_oleans(&library, &mut collected)
        .unwrap_or_else(|reason| panic!("the fixture must enumerate: {reason}"));
    assert_eq!(
        collected.len(),
        1,
        "the entry must be collected, or the refusal below is about a file the filter dropped: \
         {collected:?}"
    );

    let reason = match walk_olean_inventory(&library, Some("Fixture")) {
        Err(reason) => reason,
        Ok(accepted) => panic!(
            "a name with a gap in the middle was counted instead of refused, as {:?}",
            accepted.modules
        ),
    };
    assert!(
        reason.contains("empty segment"),
        "the refusal must name the empty segment: {reason}"
    );
    assert!(
        reason.contains("Dotted.a..b"),
        "the refusal must show the name it would have minted, so the gap is visible without \
         re-running the projection: {reason}"
    );
}

/// A fixture entry that leaves the tree is refused BEFORE anything is written.
///
/// **The parameter is called `relative_files` and nothing made it so.**
/// `Path::join` follows the caller: `base.join("/data/tmp/x.olean")` is
/// `/data/tmp/x.olean` -- the base is discarded and the write lands outside
/// `CARGO_TARGET_TMPDIR` altogether -- while `base.join("../sibling/x.olean")`
/// climbs into whatever tree sits beside this one. Both were reachable from any
/// caller, and the writer creates parent directories on the way, so neither
/// needed the target to exist first.
///
/// **It is the same hazard the name registry exists for, by a route the registry
/// cannot see.** That guard catches two tests claiming one NAME. This is two
/// tests sharing one FILE while holding different names, which the registry
/// reads as two unrelated fixtures. The symptom is identical and worse to trace:
/// a count moves in a test whose own fixture list never mentions the file.
///
/// **The obvious guard is vacuous, which is why the check is on components.**
/// `base.join("../sibling").starts_with(base)` returns TRUE: `..` is an ordinary
/// component to a lexical prefix test, and nothing on that path resolves it. A
/// containment check written that way would pass on the one input it exists to
/// catch. That is asserted below rather than described, because it is the reason
/// for the shape of the fix.
///
/// **And on components, not on the substring.** `Dotted/x..olean` -- a real
/// entry in this file, from the empty-segment fixture -- contains `..` and is
/// perfectly legal: both of its components are `Normal`. A substring test would
/// refuse a tree the walk is supposed to accept.
///
/// **The refusals are told apart by the entry they name**, since a message
/// saying only "bad fixture entry" would let the absolute cell pass on the
/// parent-directory cell's panic.
///
/// **A third entry exists for a mutant the first two cannot kill.** `..` and the
/// root both appear as the FIRST component, so a guard written as
/// `matches!(components().next(), Some(Normal(_)))` -- checking where the path
/// starts instead of what it contains -- refuses both and passes everything
/// here. `Sub/../../escaped/F.olean` starts with an ordinary name and still
/// climbs two levels out, which is measured rather than argued. Two decoys
/// chosen for two wrong rules, and a third wrong rule sitting between them: the
/// same gap the `.olean` dotfile closed in the extension filter one commit ago.
#[test]
fn a_fixture_entry_that_leaves_the_tree_is_refused_before_anything_is_written() {
    // THE MECHANISM, LEXICALLY, WITH NO FILESYSTEM INVOLVED. If either of these
    // two stops holding, the guard above is solving a problem that no longer
    // exists and the cells below are theatre.
    let base = Path::new("/fixtures/tree");
    assert_eq!(
        base.join("/data/tmp/evil.olean"),
        Path::new("/data/tmp/evil.olean"),
        "an absolute entry must DISCARD the base -- that is what makes it an escape rather than a \
         nested path"
    );
    assert!(
        base.join("../sibling/F.olean").starts_with(base),
        "`starts_with` must still accept the escaping path; if it has learned to resolve `..`, \
         the containment check this guard replaced is no longer vacuous and the fix can be \
         simplified"
    );

    let refuse = |name: &str, entry: &str| -> String {
        let previous = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let outcome = std::panic::catch_unwind(|| write_inventory_fixture(name, &[entry]));
        std::panic::set_hook(previous);
        let payload = outcome
            .err()
            .unwrap_or_else(|| panic!("`{entry}` must be refused, not written"));
        payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .unwrap_or_default()
            .to_string()
    };

    // NOTHING MAY LAND. The two targets are named here so their absence can be
    // checked afterwards: a refusal that arrives after the write would still
    // produce a panic and would still pass a message assertion.
    let tmp = Path::new(env!("CARGO_TARGET_TMPDIR"));
    let escaped_sibling = tmp.join("t6r7-escaped-sibling");
    let outside_target = tmp.join("t6r7-outside-target-marker.olean");

    // The absolute entry points INSIDE the target directory on purpose. It is
    // outside the fixture tree, which is all this cell is about, and if the
    // guard ever regressed the stray write lands in `target/` rather than
    // somewhere a test has no business touching.
    let outside_entry = outside_target
        .to_str()
        .unwrap_or_else(|| panic!("{} is not UTF-8", outside_target.display()));
    let climbed = refuse(
        "t6r7-selftest-escape-parent-v1",
        "../t6r7-escaped-sibling/Foo.olean",
    );
    let absolute = refuse("t6r7-selftest-escape-absolute-v1", outside_entry);
    // THE ESCAPE THAT DOES NOT START AT THE FIRST COMPONENT. Both entries above
    // put the offending component first -- `..` and the root -- so a guard that
    // examined only `components().next()` refuses both and survives every
    // assertion in this test. Measured: this entry's first component is an
    // ordinary name, and it still climbs two levels out of the tree.
    let deep = refuse(
        "t6r7-selftest-escape-deep-v1",
        "Sub/../../t6r7-escaped-deep/Foo.olean",
    );

    // ASSERTED ON THE PART THAT DIFFERS: both refusals share every word except
    // the entry, so each cell must find its own and not the other's.
    assert!(
        climbed.contains("../t6r7-escaped-sibling/Foo.olean") && !climbed.contains(outside_entry),
        "the parent-directory refusal must name its own entry: {climbed}"
    );
    assert!(
        absolute.contains(outside_entry) && !absolute.contains("../t6r7-escaped-sibling/Foo.olean"),
        "the absolute refusal must name its own entry: {absolute}"
    );

    assert!(
        deep.contains("Sub/../../t6r7-escaped-deep/Foo.olean"),
        "the deep refusal must name its own entry: {deep}"
    );

    assert!(
        !escaped_sibling.exists(),
        "the entry was refused and a directory still appeared at {}; the check must run BEFORE \
         `create_dir_all`, or the refusal is an announcement about a write that already happened",
        escaped_sibling.display()
    );
    // The deep entry resolves to a SIBLING of the fixture tree, two levels up:
    // `<tmp>/<fixture>/Sub/../..` is `<tmp>`. `create_dir_all` walks that chain
    // and would have created the directory outside.
    assert!(
        !tmp.join("t6r7-escaped-deep").exists(),
        "an escape whose `..` is not its first component still left {} behind",
        tmp.join("t6r7-escaped-deep").display()
    );
    assert!(
        !outside_target.exists(),
        "the absolute entry was refused and a file still appeared at {}, outside the fixture tree",
        outside_target.display()
    );

    // GREEN CONTROL, ON BOTH HALVES. A nested entry must still be written, and
    // an entry CONTAINING `..` inside a component must still be legal -- the
    // rule is about components, not about the two characters.
    let ok = write_inventory_fixture(
        "t6r7-selftest-escape-ok-v1",
        &["Sub/Inner.olean", "Dotted/x..olean"],
    );
    for entry in ["Sub/Inner.olean", "Dotted/x..olean"] {
        let written = ok.join(entry);
        assert!(
            written.is_file(),
            "`{entry}` is a plain relative entry and must still be written: {}",
            written.display()
        );
        // CONTAINMENT, RESOLVED RATHER THAN LEXICAL -- the check `starts_with`
        // could not do above.
        let real = written
            .canonicalize()
            .unwrap_or_else(|error| panic!("canonicalize {}: {error}", written.display()));
        let root = ok
            .canonicalize()
            .unwrap_or_else(|error| panic!("canonicalize {}: {error}", ok.display()));
        assert!(
            real.starts_with(&root),
            "`{entry}` was written to {} , which is not below the fixture tree {}",
            real.display(),
            root.display()
        );
    }
}

/// What a module name MEANS, written out independently of how it is computed.
///
/// **Why not just call the projection.** The parallel-vectors test used to
/// recompute each expected name by calling `module_name_from_path` -- the very
/// function whose output it was checking. That is a mirror: replace the
/// projection with a stub returning a constant and both sides change together,
/// so the assertion holds while the projection is wrong. It survived only
/// because the injectivity rule inside the walk would fail first, which is
/// protection by a neighbour rather than by the check itself.
///
/// **This is the specification half of the pair.** It states the meaning -- a
/// module name is its path below the library root, with the trailing `.olean`
/// removed and the components joined by dots, under the namespace -- using none
/// of the projection's own machinery. In particular it does NOT use
/// `Path::with_extension`, so a change to what counts as "the extension" is a
/// disagreement between the two rather than a change both follow.
///
/// Deliberate duplication, like the corpus root path that is written once as a
/// constant and once as a literal: one side is the implementation, the other is
/// what the implementation is supposed to mean.
fn expected_module_name(base: &Path, path: &Path, prefix: &str) -> String {
    let relative = path
        .strip_prefix(base)
        .unwrap_or_else(|_| panic!("{} is not below {}", path.display(), base.display()));
    let mut parts = relative
        .components()
        .map(|component| component.as_os_str().to_string_lossy().into_owned())
        .collect::<Vec<_>>();
    let last = parts
        .last_mut()
        .unwrap_or_else(|| panic!("{} has no components", relative.display()));
    *last = last
        .strip_suffix(".olean")
        .unwrap_or_else(|| panic!("the walk collects only `.olean` files, but found `{last}`"))
        .to_string();
    format!("{prefix}.{}", parts.join("."))
}

/// `oleans` and `modules` are PARALLEL: `modules[i]` is the projection of
/// `oleans[i]`, and the extension match is exact.
///
/// **Two enumerations, joined by a length check.** `walk_olean_inventory` walks
/// the tree with `collect_present_oleans`, and then `module_names_below` walks
/// it AGAIN internally. The two results are returned side by side in one struct,
/// whose shape invites a caller to zip them -- and the only thing relating them
/// is that their lengths match. Equal lengths are not correspondence: two
/// same-sized vectors in different orders satisfy that check perfectly, and a
/// consumer zipping them would attribute every module to the wrong file while
/// every count stayed right.
///
/// **It USED to be a coincidence, and this doc used to say so.** The walk called
/// `module_names_below`, which enumerated the tree a second time; both vectors
/// came out in path order and corresponded because two independent sweeps
/// happened to sort the same way. The walk now projects the paths it already
/// holds, so the correspondence is structural. What this test still earns is the
/// MEANING: the assertion recomputes each name from its own path rather than
/// comparing against a hardcoded list, so a projection replaced by a stub fails
/// here instead of agreeing with itself.
///
/// **The extension match is exact, checked from both sides.** `Ignored.OLEAN`
/// differs only in case and `NoExtension` has none at all; both must be absent.
/// A filter written with `eq_ignore_ascii_case`, or one testing "contains a dot",
/// would pull unrelated files into the corpus and inflate every count taken from
/// it.
#[test]
fn the_inventory_vectors_are_parallel_and_the_extension_match_is_exact() {
    let library = write_inventory_fixture(
        "t6r7-inventory-parallel-v1",
        &[
            "Zeta.olean",
            "Alpha/Beta.olean",
            "Alpha/Alpha.olean",
            "Mid.dotted/Leaf.olean",
            "Ignored.OLEAN",
            "NoExtension",
        ],
    );

    // SAME ARGUMENT, AND SHARPER HERE. The rejection check below is written as
    // `!any(...)`, which an ABSENT decoy satisfies perfectly -- delete the two
    // entries and the loop proves that nothing which is not there was not
    // collected. Their presence on disk is what makes it a test.
    for decoy in ["Ignored.OLEAN", "NoExtension"] {
        assert!(
            library.join(decoy).is_file(),
            "the decoy `{decoy}` is missing from the fixture, so the exactness check below is \
             satisfied by its absence rather than by the filter"
        );
    }

    let OleanInventory { oleans, modules } = walk_olean_inventory(&library, Some("Fixture"))
        .unwrap_or_else(|reason| panic!("the parallel fixture must be walkable: {reason}"));

    assert_eq!(
        oleans.len(),
        4,
        "only the four lowercase `.olean` FILES are oleans; `Ignored.OLEAN` differs in case and \
         `NoExtension` has none. Found: {oleans:?}"
    );
    for rejected in ["Ignored.OLEAN", "NoExtension"] {
        assert!(
            !oleans.iter().any(|path| path.ends_with(rejected)),
            "`{rejected}` was collected. The extension test must be exact equality on `olean`, \
             not a case-insensitive or substring match, or unrelated files join the corpus and \
             inflate every count taken from it: {oleans:?}"
        );
    }

    // ANTI-VACUITY. Correspondence over one element, or over elements whose
    // order cannot differ, states almost nothing. The tree must hold siblings
    // under one parent and a directory carrying a dot before the relation below
    // is worth checking.
    assert!(
        modules
            .iter()
            .filter(|name| name.starts_with("Fixture.Alpha."))
            .count()
            >= 2,
        "the fixture must hold two modules under one parent: {modules:?}"
    );
    assert!(
        modules.iter().any(|name| name.contains("Mid.dotted")),
        "the fixture must hold a dotted directory: {modules:?}"
    );

    // THE RELATION, recomputed per element from the path it is supposed to come
    // from -- not compared against a list somebody typed.
    assert_eq!(modules.len(), oleans.len());
    for (index, path) in oleans.iter().enumerate() {
        // Computed from the path by the SPECIFICATION, not by the projection
        // under test -- otherwise a stubbed projection would agree with itself.
        let expected = expected_module_name(&library, path, "Fixture");
        assert_eq!(
            modules[index],
            expected,
            "modules[{index}] is `{}` but oleans[{index}] is {}, which projects to `{expected}`. \
             The two vectors are returned side by side and callers zip them; equal LENGTHS do not \
             make them correspond, and a reordering here would attribute every module to the \
             wrong file while every count stayed correct",
            modules[index],
            path.display()
        );
    }
}

/// A tree with NO oleans walks clean, so "the walk succeeded" carries no
/// information about whether anything was found -- and the receipt floor is the
/// only thing that notices.
///
/// **Why this is worth an assertion rather than a shrug.** Every check inside
/// `walk_olean_inventory` is a statement about the entries it found: the prefix
/// check is an `Option`-guarded loop over the names, the injectivity check
/// compares two counts, and both are VACUOUSLY satisfied when the population is
/// empty. `all()` over nothing is true; `0 == 0` is true. So a directory holding
/// no oleans is not merely accepted, it is accepted by every rule the walk has,
/// and it is indistinguishable from a corpus by anything the walk returns except
/// the count itself.
///
/// **That is correct, and it is also the whole exposure.** An empty walk must not
/// be an error -- a subdirectory with no oleans is ordinary, and a walk that
/// refused one could not recurse. The consequence is that NOTHING in the walk
/// stands between an empty tree and a whole-Mathlib claim. The floor in
/// `WholeMathlibReceipt::validate` is the sole guard, and this test pins that by
/// carrying the empty population all the way to a receipt and requiring the
/// refusal to name the closure-module floor specifically. Move or relax that
/// floor and this test goes red, which is the point: today the protection lives
/// in exactly one place and nothing else would notice its absence.
///
/// **The fixture holds a file, deliberately.** A directory with no entries at all
/// and a directory whose entries are simply not oleans must both walk to nothing,
/// and the second is the case that actually occurs in a real tree. The first half
/// of that sentence was unbacked when it was written -- the fixture writer only
/// ever created directories as the PARENT of an entry, so a tree with no entries
/// at all could not be built and was never walked. It can now, and
/// `an_empty_library_walks_to_nothing_and_a_missing_one_does_not_walk` is where
/// it is checked.
#[test]
fn a_tree_with_no_oleans_walks_clean_and_only_the_receipt_floor_refuses_it() {
    let library = write_inventory_fixture("t6r7-inventory-empty-v1", &["notes.txt", "Sub/read.me"]);

    let OleanInventory { oleans, modules } = walk_olean_inventory(&library, Some("Fixture"))
        .unwrap_or_else(|reason| {
            panic!(
                "a tree with no oleans must not be an ERROR -- an ordinary subdirectory holds \
                 none, and a walk that refused one could not recurse at all: {reason}"
            )
        });
    assert!(
        oleans.is_empty() && modules.is_empty(),
        "nothing here is an olean; found {oleans:?} / {modules:?}"
    );

    // The empty population satisfies the live conservation law too, which is the
    // same vacuity one level up.
    let counts = CorpusCounts::default();
    counts.assert_conservation("empty inventory");

    let spec = CorpusReceiptSpec {
        bead: "franken_lean-t6r7",
        corpus_commit: suite_lock_corpus_commit(),
        seed_modules: modules.len() as u64,
        receipt_path_var: "FLN_WHOLE_MATHLIB_RECEIPT",
    };
    let receipt = WholeMathlibReceipt::from_run(&WholeMathlibRunFacts {
        spec: &spec,
        counts: &counts,
        closure_modules: oleans.len() as u64,
        corpus_fixture_hash: "an-empty-tree-is-not-a-corpus",
        observed_unix_s: 1_786_333_444,
        wall_ms: 1,
    });
    assert_eq!(receipt.closure_modules, 0);
    assert_eq!(receipt.seed_modules, 0);
    assert_eq!(receipt.decoded, 0);
    assert_eq!(receipt.compared, 0);

    let reason = match receipt.validate(&suite_lock_reference_pin(), &suite_lock_corpus_commit()) {
        Err(reason) => reason,
        Ok(()) => panic!(
            "an EMPTY tree was accepted as a whole-Mathlib observation. Zero divergences over zero \
             modules is the empty-referent row in its purest form, and the walk cannot catch it: \
             every rule the walk has is vacuously true over an empty population."
        ),
    };
    assert!(
        reason.contains("closure module(s)") && reason.contains("below the"),
        "the refusal must come from the size floor, because that is the ONLY rule anywhere that \
         distinguishes an empty tree from a corpus: {reason}"
    );
}

/// An EMPTY library walks to nothing; a MISSING one does not walk at all.
///
/// **The neighbouring test names both cases and could only build one.** Its doc
/// says a directory with no entries and a directory whose entries are not oleans
/// must both walk to nothing, and its fixture holds `notes.txt` -- because the
/// writer created directories only as the PARENT of an entry, so asking for no
/// entries created nothing. A caller who did that got back a path to a
/// directory that was never made, and the walk answered `read corpus directory
/// ...: No such file or directory`. The half of the claim about an empty tree
/// had no fixture behind it, and the failure it would have produced points at
/// the filesystem rather than at the tree.
///
/// **Absent and empty are different everywhere else in this file.** The corpus
/// classifier separates an absent root from a misprovisioned one so the first
/// can skip and the second must fail. The retained-receipt reader separates a
/// file that is not there from one it cannot read, so nothing announces "no
/// receipt is retained" about a file sitting right there. This was the third
/// instance of the same distinction and the only one where the two collapsed
/// into one outcome.
///
/// **Both roots are walked here, and they are told apart by what they return**,
/// not by a message fragment they might come to share: the empty tree returns
/// `Ok` with a population of zero, the missing tree returns `Err`. A cell that
/// asserted only "the empty tree does not panic" would pass on the old
/// behaviour, since a failed walk returns `Err` rather than unwinding.
#[test]
fn an_empty_library_walks_to_nothing_and_a_missing_one_does_not_walk() {
    let empty = write_inventory_fixture("t6r7-inventory-nothing-at-all-v1", &[]);

    assert!(
        empty.is_dir(),
        "a fixture asked for no entries must still be a TREE. {} does not exist, so its caller \
         would be told the corpus is unreadable rather than that the library holds no modules",
        empty.display()
    );

    // ANTI-VACUITY: the tree must really hold nothing. If some earlier shape had
    // left files under this name, the zero below would be a filter's answer over
    // a populated tree rather than the empty walk this test is about.
    let entries = fs::read_dir(&empty)
        .unwrap_or_else(|error| panic!("read {}: {error}", empty.display()))
        .count();
    assert_eq!(
        entries,
        0,
        "{} holds {entries} entr(ies); this test is about a tree with NOTHING in it",
        empty.display()
    );

    let walked = walk_olean_inventory(&empty, Some("Fixture"))
        .unwrap_or_else(|reason| panic!("an empty library must walk, not fail: {reason}"));
    assert!(
        walked.oleans.is_empty() && walked.modules.is_empty(),
        "an empty tree must project to an empty inventory, not to a phantom module: {:?} / {:?}",
        walked.oleans,
        walked.modules
    );

    // THE PART THAT DIFFERS. A root that was never created must still fail, and
    // fail as a filesystem fault -- otherwise this change would have turned a
    // missing corpus into a silently empty one, which is the far worse error and
    // exactly what the floor in `WholeMathlibReceipt::validate` exists to catch
    // downstream.
    let missing = empty.join("never-created");
    let reason = match walk_olean_inventory(&missing, Some("Fixture")) {
        Err(reason) => reason,
        Ok(accepted) => panic!(
            "a directory that does not exist walked to an inventory of {} module(s); an absent \
             tree must never read as an empty one",
            accepted.modules.len()
        ),
    };
    assert!(
        reason.contains("read corpus directory") && reason.contains("never-created"),
        "the refusal must say which directory could not be read, or an absent root is \
         indistinguishable from an empty one in the log as well as in the return value: {reason}"
    );
}

/// A ONE-MODULE set cannot have a cross-module conflict, so the two check-olean
/// paths must diverge -- and the divergence is a property of SET SIZE, not of the
/// module.
///
/// **What is actually new here.** After `134defc3` the directory case expects
/// `declaration-closure` with the set-wide conflict, and the single-module case
/// twenty lines up expects `unresolved-imports`. Both are asserted positively and
/// separately, and nothing states the thing that makes them consistent: the
/// conflict scan compares declarations across DISTINCT modules, so a set of one
/// has nothing to conflict with. That is not a style preference, it is the only
/// reason the two paths are allowed to differ.
///
/// **The negative is the load-bearing half.** If a single-module invocation ever
/// reported `ConflictingModuleDeclaration`, the module would have been counted as
/// more than one member of the set -- which is exactly the companion parts being
/// treated as separate modules, the regression this whole test family exists to
/// catch. That failure would otherwise be invisible: the run would still exit 1,
/// still refuse the input, and still look like a healthy rejection. So the
/// conflict's own rendering is asserted ABSENT here, against the same string the
/// directory case asserts PRESENT.
///
/// **Evidence status, stated because it differs from the previous commit's.** The
/// positive half is backed by an observation rather than a reading: w4 ran this
/// pinned module through the single-module path and the `unresolved-imports`
/// assertion passed, while only the directory assertion failed. The negative half
/// is not observed and is a genuine prediction -- if it is wrong, this test fails
/// and names a companion-association defect rather than passing quietly.
#[test]
fn a_one_module_set_reports_unresolved_imports_and_never_a_conflict() {
    let Some(reference_lib) = reference_lib() else {
        // A TYPED skip, unlike the bare `return` the neighbouring test uses. A
        // silent early return is a green that asserted nothing, and nothing in
        // its output distinguishes "the pin is missing" from "the property
        // holds".
        println!(
            "{{\"schema\":\"fln-t6r7-check-olean-paths/1\",\"status\":\"skipped_absent_host_input\",\
             \"required_path\":{},\"override_env\":\"FLN_REFERENCE_LIB\",\
             \"claims\":\"NOTHING. The pinned Reference library is not on this host, so neither \
             check-olean path was exercised.\"}}",
            json_string(
                "~/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean (or $FLN_REFERENCE_LIB)"
            ),
        );
        return;
    };
    let module = reference_lib.join("Init/Data/List/ToArrayImpl.olean");
    assert!(
        module.is_file(),
        "the pinned module this property is stated over is missing: {}",
        module.display()
    );

    // ONE MODULE. Its imports are outside the set, so the set is not closed and
    // the run is refused for that -- the outcome the pin has always produced.
    let single = fln_cli::run([
        std::ffi::OsString::from("check-olean"),
        std::ffi::OsString::from("--json"),
        module.clone().into_os_string(),
    ]);
    assert_eq!(single.exit_code, 1, "{}", single.stderr);
    assert!(
        single.stderr.contains("\"class\":\"unresolved-imports\""),
        "a single module's imports are outside its own set, so the refusal must still be the \
         unresolved-imports one: {}",
        single.stderr
    );
    assert!(
        !single
            .stderr
            .contains("decode to different declarations both named"),
        "a ONE-MODULE set reported a cross-module declaration conflict. The scan compares \
         declarations between DISTINCT modules, so this can only mean the module was counted as \
         several members -- its companion parts treated as separate modules, which is the \
         association defect this test family guards. The run would still exit 1 and still look \
         like a healthy refusal, which is why this is asserted rather than assumed: {}",
        single.stderr
    );

    // THE SAME MODULE, in a set large enough to conflict. The input did not
    // change; only how many modules are being planned together did.
    let directory = module
        .parent()
        .expect("the pinned module has a library directory")
        .to_path_buf();
    let many = fln_cli::run([
        std::ffi::OsString::from("check-olean"),
        std::ffi::OsString::from("--json"),
        directory.into_os_string(),
    ]);
    assert_eq!(many.exit_code, 1, "{}", many.stderr);
    assert_ne!(
        single.stderr, many.stderr,
        "the one-module and many-module paths produced identical output. They are refused for \
         different reasons at different stages, and if they ever agree then either the set-wide \
         scan stopped running or the single-module path started being treated as a set"
    );
}

/// Namespace qualification is a UNIFORM prefix, at every depth.
///
/// **What depends on this.** The names this projection produces are matched
/// against the import lists recorded inside the oleans themselves, and
/// `closed_whole_mathlib_corpus` REFUSES to proceed when any import fails to
/// resolve. If qualification were ever non-uniform -- applied to top-level
/// modules but not to nested ones, say, which is the shape a `split` or a
/// depth-sensitive branch drifts into -- then nested imports alone would stop
/// resolving. The lane would not report "the qualifier is wrong"; it would
/// report unresolved imports for a subset of the corpus, and the failure would
/// look like a corpus-integrity problem in modules nobody had touched.
///
/// **Why two walks and not one expectation.** Comparing against a hand-written
/// list would pin the names, not the RELATION. This walks one unchanged tree
/// twice, once unqualified and once qualified, and requires the second to be the
/// first with one prefix in front of it -- every element, no exceptions. That is
/// the property the import matching actually rests on, and it holds or fails
/// independently of what the names happen to be.
///
/// **The tree spans depths on purpose.** "Uniform across depths" tested at one
/// depth is not tested at all, so the fixture is asserted to contain both a
/// top-level module and one nested two levels down before the relation is
/// checked. Without those two assertions this test would keep passing over a
/// flattened fixture while saying nothing about the case that breaks.
#[test]
fn namespace_qualification_is_a_uniform_prefix_at_every_depth() {
    let library = write_inventory_fixture(
        "t6r7-inventory-prefix-v1",
        &["Top.olean", "Deep/Down/Leaf.olean", "Mid/Node.olean"],
    );

    let bare = walk_olean_inventory(&library, None)
        .unwrap_or_else(|reason| panic!("the fixture tree must walk unqualified: {reason}"));
    let qualified = walk_olean_inventory(&library, Some("Ns"))
        .unwrap_or_else(|reason| panic!("the fixture tree must walk qualified: {reason}"));

    // ANTI-VACUITY, before the relation: the tree must actually span depths, or
    // "uniform at every depth" is a claim about one depth.
    assert!(
        bare.modules.iter().any(|name| !name.contains('.')),
        "the fixture must hold a top-level module, or depth uniformity is untested: {:?}",
        bare.modules
    );
    assert!(
        bare.modules
            .iter()
            .any(|name| name.matches('.').count() >= 2),
        "the fixture must hold a module nested at least two levels deep, or depth uniformity is \
         untested: {:?}",
        bare.modules
    );

    assert_eq!(
        bare.oleans, qualified.oleans,
        "the same tree was walked twice; the file set cannot depend on the namespace"
    );
    assert_eq!(
        bare.modules.len(),
        qualified.modules.len(),
        "qualification must not add or drop modules"
    );
    for (unqualified, name) in bare.modules.iter().zip(&qualified.modules) {
        assert_eq!(
            name,
            &format!("Ns.{unqualified}"),
            "qualification must be exactly one prefix on every module. `{unqualified}` became \
             `{name}`, which is not `Ns.` in front of it -- and a qualifier that treats some \
             depths differently makes nested imports alone fail to resolve, which reads as a \
             corpus-integrity problem rather than as a naming bug"
        );
    }
}

/// A DIRECTORY named `*.olean` is traversed, never counted as a module.
///
/// **The hazard is an ordering, and orderings rot silently.** The walk tests
/// `is_dir()` BEFORE it tests the extension, so a directory called
/// `Nested.olean` is recursed into and only the files beneath it are collected.
/// Swap those two tests -- a plausible tidy-up, since one reads as "filter by
/// extension" and the other as "recurse" -- and the directory itself is pushed
/// onto the olean list. It then projects to a module name like any file would,
/// so the inventory grows a module that is a FOLDER: a declaration count is
/// taken for something with no declarations, and the corpus reports a member it
/// does not have.
///
/// **The assertion is the counterfactual, not a total.** Checking only "three
/// oleans" would fail for many unrelated reasons and would not say WHICH
/// mistake was made. Under the reordering above the extra module is exactly
/// `Fixture.Nested` -- the directory's own name with its extension dropped -- so
/// the test names that string and says what its presence would mean. A count
/// alone diagnoses nothing; a named counterfactual diagnoses one thing.
///
/// **`Nested.olean.Inner` is the correct answer, odd as it reads.** The
/// projection strips only the FINAL extension, so a directory carrying a dot in
/// its name contributes both of its dotted parts to the module path. That is
/// what the pin's own naming would produce for such a tree, and pinning it here
/// means a future change to the projection cannot quietly redefine it.
#[test]
fn a_directory_named_like_an_olean_is_walked_through_not_counted() {
    let library = write_inventory_fixture(
        "t6r7-inventory-dotted-dir-v1",
        &["Real.olean", "Nested.olean/Inner.olean", "Plain/Deep.olean"],
    );

    let OleanInventory { oleans, modules } = walk_olean_inventory(&library, Some("Fixture"))
        .unwrap_or_else(|reason| panic!("the dotted-directory fixture must be walkable: {reason}"));

    assert_eq!(
        oleans.len(),
        3,
        "the three FILES are oleans; the directory that merely shares their extension is not. \
         Found: {oleans:?}"
    );
    assert_eq!(
        modules,
        vec![
            "Fixture.Nested.olean.Inner".to_string(),
            "Fixture.Plain.Deep".to_string(),
            "Fixture.Real".to_string(),
        ],
        "the walk must recurse through a dotted directory and keep only the files below it"
    );
    assert!(
        !modules.iter().any(|name| name == "Fixture.Nested"),
        "`Fixture.Nested` is present, which means the directory `Nested.olean` was collected as \
         though it were an olean. That is what happens if the extension test is run before the \
         is_dir test: the inventory gains a module that is a folder, and a declaration count is \
         attributed to something with no declarations."
    );
}

/// Write an olean whose FILE NAME is not valid UTF-8.
///
/// Only the stem is invalid: the extension stays `olean` so the entry is
/// genuinely collected by the walk's filter and reaches the projection. A name
/// that failed the extension test would be skipped for the wrong reason and
/// would prove nothing about the branch under test.
#[cfg(unix)]
fn write_non_utf8_olean(dir: &Path) -> PathBuf {
    use std::os::unix::ffi::OsStrExt;
    let path = dir.join(std::ffi::OsStr::from_bytes(b"Bad\xFF.olean"));
    fs::write(&path, b"").unwrap_or_else(|error| panic!("create non-UTF-8 fixture entry: {error}"));
    path
}

/// An entry whose name is not UTF-8 is REFUSED, never quietly dropped.
///
/// **The two ways this could go, and why only one is acceptable.** The name has
/// to become a module name, and it cannot. A projection that skipped what it
/// could not decode would return a smaller inventory and no error -- and a
/// smaller number is invisible here, because it looks exactly like a smaller
/// corpus rather than like a file the walk gave up on. That is the
/// filter-that-continues-is-a-sampler defect: the denominator silently changes
/// and every count downstream is quietly about a different population. The only
/// honest outcome is a typed refusal naming the entry.
///
/// **It is collected before it is refused, which is the point.** The extension
/// is valid UTF-8 (`olean`), so the walk's filter accepts the entry and the
/// failure happens in the projection, where it belongs. A fixture whose name
/// failed the extension test would be skipped for an unrelated reason and would
/// witness nothing.
///
/// **A good file sits beside it**, so the refusal cannot be "this walk fails on
/// any tree", and so the test also says that ONE bad entry poisons the whole
/// inventory rather than yielding a partial one. A partial inventory is the
/// under-count above, wearing a success.
///
/// Unix only: a non-UTF-8 filename cannot be constructed portably. Stated rather
/// than hidden -- elsewhere the behaviour is unverified, not verified.
#[cfg(unix)]
#[test]
fn the_inventory_walk_refuses_an_entry_whose_name_is_not_utf8() {
    let library = write_inventory_fixture("t6r7-inventory-non-utf8-v1", &["Good.olean"]);
    write_non_utf8_olean(&library);

    let reason = match walk_olean_inventory(&library, Some("Fixture")) {
        Err(reason) => reason,
        Ok(OleanInventory { oleans, modules }) => panic!(
            "the walk ACCEPTED a tree holding an entry it cannot name: {} olean(s) became \
             {modules:?}. If the unnameable entry was dropped, the inventory is short by exactly \
             the files it gave up on and nothing downstream can tell that from a smaller corpus.",
            oleans.len()
        ),
    };
    assert!(
        reason.contains("non-UTF-8"),
        "the refusal must name the undecodable path rather than fail for something incidental: \
         {reason}"
    );
    // AND IT MUST NAME THE RIGHT ENTRY. The message carries the path, so a walk
    // that refused correctly but reported the WRONG file -- the first entry, say,
    // or whichever it happened to be holding -- would satisfy the check above
    // while sending whoever repairs the corpus to a file that is fine. `Bad\u{FFFD}`
    // is how the undecodable stem renders lossily; `Good` is the neighbour that
    // must not be blamed.
    assert!(
        reason.contains("Bad") && !reason.contains("Good"),
        "the refusal names the wrong entry: {reason}"
    );
}

/// A symlinked FILE is refused, so the inventory cannot include something that
/// is not in the pinned tree.
///
/// **Why this is an identity law and not a hygiene rule.** The corpus's whole
/// job is to say which declarations are in it. A symlink resolves to bytes that
/// live somewhere else -- another checkout, another revision, a scratch
/// directory, anything -- so following one would let the walk report a module
/// that is not part of the corpus it claims to describe, and every count and
/// digest derived from that walk would then describe a tree that does not exist
/// as checked out. `preflight_mathlib_corpus` already refuses a symlinked ROOT;
/// this is the same law one level down, where a single entry can smuggle in a
/// file the root check never sees.
///
/// **It had never executed.** The refusal has exactly one site, inside
/// `collect_present_oleans`, and nothing anywhere reached it -- so "the corpus
/// refuses symlinks" was a sentence in a `format!` string rather than a
/// behaviour anyone had observed.
///
/// Unix only, and stated rather than hidden: the law is real on every platform,
/// but this control cannot construct its input where `std::os::unix` does not
/// exist, so on such a host the behaviour is unverified rather than verified.
#[cfg(unix)]
#[test]
fn the_inventory_walk_refuses_a_symlinked_file_entry() {
    let library = write_inventory_fixture("t6r7-inventory-symlink-file-v1", &["Real.olean"]);
    // Sorted before `Real.olean`, so the walk meets the link first and the
    // refusal cannot be an accident of iteration order.
    link_fixture_entry(&library.join("Alias.olean"), &library.join("Real.olean"));

    let reason = match walk_olean_inventory(&library, Some("Fixture")) {
        Err(reason) => reason,
        Ok(OleanInventory { oleans, modules }) => panic!(
            "the walk FOLLOWED a symlinked olean: {} entr(y/ies) became {modules:?}. A link \
             resolves to bytes outside the tree being inventoried, so the corpus would then \
             contain a module that is not in it.",
            oleans.len()
        ),
    };
    assert!(
        reason.contains("symlink"),
        "the refusal must name the symlink rather than fail for something incidental: {reason}"
    );
    // WHICH entry, not just that one was refused. Both symlink cells assert the
    // same word on the same production message, so the entry name is the only
    // part that differs between them -- and it is the part that would be wrong
    // if the walk reported some other entry as the link.
    assert!(
        reason.contains("Alias.olean") && !reason.contains("Real.olean"),
        "the refusal must blame the planted link, not the real olean beside it: {reason}"
    );
}

/// A symlinked DIRECTORY is refused too, which is the case that matters more.
///
/// A linked file smuggles in one module; a linked directory smuggles in an
/// entire subtree, and could point at a second corpus at a different revision.
/// The check is the same one, but a guard shown to reject only the smaller case
/// has not been shown to reject the larger one -- `is_symlink()` is tested
/// before `is_dir()`, and an implementation that reordered them would keep
/// passing the file control while silently walking a linked subtree.
#[cfg(unix)]
#[test]
fn the_inventory_walk_refuses_a_symlinked_directory_entry() {
    let library = write_inventory_fixture(
        "t6r7-inventory-symlink-dir-v1",
        &["Real.olean", "Sub/Inner.olean"],
    );
    // `Aliased` sorts before both `Real.olean` and `Sub`.
    link_fixture_entry(&library.join("Aliased"), &library.join("Sub"));

    let reason = match walk_olean_inventory(&library, Some("Fixture")) {
        Err(reason) => reason,
        Ok(OleanInventory { oleans, modules }) => panic!(
            "the walk RECURSED THROUGH a symlinked directory: {} olean(s) became {modules:?}. \
             A linked subtree can carry an entire second corpus at another revision.",
            oleans.len()
        ),
    };
    assert!(
        reason.contains("symlink"),
        "the refusal must name the symlink rather than fail for something incidental: {reason}"
    );
    assert!(
        reason.contains("Aliased") && !reason.contains("Real.olean"),
        "the refusal must blame the linked directory, not a real entry beside it: {reason}"
    );
}

/// A real inventory flows into a real receipt, and the real guard refuses it.
///
/// **The join that did not exist.** The producer test drives `from_run` with a
/// hand-built `CorpusCounts` and hand-picked module counts; the walk tests drive
/// `walk_olean_inventory` over a real tree and stop at its output. Nothing
/// connected the two, so "the row carries what the walk observed" was an
/// assumption sitting in the exact gap between two passing tests. Here the
/// numbers come out of the filesystem, go through the production producer, and
/// are compared against what was on disk.
///
/// **Why the guard must REFUSE the result, and why that is the point.** Three
/// empty files are not Mathlib. A receipt built from them is exactly the
/// empty-referent row `validate` exists to catch, so this is the anti-vacuity
/// floor tested against a REAL small tree rather than against a number somebody
/// typed. If the floor were ever weakened, a fixture would start qualifying as a
/// whole-corpus observation and this test says so.
///
/// **What it does not claim.** Nothing about Mathlib, the corpus, the kernel or
/// the oracle. No declaration is decoded and none is checked.
#[test]
fn a_fixture_inventory_flows_into_a_receipt_the_guard_refuses() {
    let library = write_inventory_fixture(
        "t6r7-receipt-identity-v1",
        &[
            "Alpha.olean",
            "Nested/Beta.olean",
            "Nested/Gamma.olean",
            "Alpha.olean.server",
            "ignored.txt",
        ],
    );

    // DETERMINISM, on real directory entries. `read_dir` yields in whatever
    // order the filesystem likes; the walk sorts. Two walks of one unchanged
    // tree must agree, or every count derived from one of them is a coin toss.
    let first = walk_olean_inventory(&library, Some("Fixture"))
        .unwrap_or_else(|reason| panic!("the fixture tree must be walkable: {reason}"));
    let second = walk_olean_inventory(&library, Some("Fixture"))
        .unwrap_or_else(|reason| panic!("the fixture tree must be walkable twice: {reason}"));
    assert_eq!(
        first.modules, second.modules,
        "two walks of an unchanged tree disagreed; the projection is not order-deterministic and \
         any count taken from it is arbitrary"
    );
    assert_eq!(first.oleans, second.oleans);

    // The population is DERIVED from the tree, not chosen. This is the shape the
    // driver produces for modules whose import context it cannot rebuild:
    // everything decoded, nothing compared, every row a subject non-answer under
    // one named family.
    let observed = first.modules.len() as u64;
    assert_eq!(observed, 3, "the fixture tree holds exactly three oleans");
    let mut counts = CorpusCounts {
        decoded: observed,
        unscorable: observed,
        subject_no_answer: observed,
        ..CorpusCounts::default()
    };
    counts
        .no_answer_families
        .insert(FAMILY_UNFAITHFUL_IMPORT_CONTEXT.to_string(), observed);
    // The live law, over a population that came off a disk rather than out of a
    // literal.
    counts.assert_conservation("fixture inventory");

    let spec = CorpusReceiptSpec {
        bead: "franken_lean-t6r7",
        corpus_commit: suite_lock_corpus_commit(),
        seed_modules: observed,
        receipt_path_var: "FLN_WHOLE_MATHLIB_RECEIPT",
    };
    let receipt = WholeMathlibReceipt::from_run(&WholeMathlibRunFacts {
        spec: &spec,
        counts: &counts,
        closure_modules: observed,
        corpus_fixture_hash: "fixture-tree-which-is-not-a-corpus",
        observed_unix_s: 1_786_222_333,
        wall_ms: 7,
    });

    // THE IDENTITY: the row says what the walk saw.
    assert_eq!(
        receipt.seed_modules, observed,
        "the row's seed count must be the number of modules the walk actually found"
    );
    assert_eq!(receipt.closure_modules, observed);
    assert_eq!(receipt.decoded, observed);
    assert_eq!(receipt.unscorable, observed);
    assert_eq!(receipt.subject_no_answer, observed);
    assert_eq!(receipt.compared, 0);
    assert_eq!(
        receipt.no_answer_families,
        vec![format!("{FAMILY_UNFAITHFUL_IMPORT_CONTEXT}={observed}")],
        "the triage must carry the family the counts were built from, at the count they were \
         built with"
    );
    assert!(
        receipt.restrictive_families.is_empty(),
        "nothing was compared, so nothing can be a restrictive divergence"
    );

    // THE REFUSAL, and specifically for being too small.
    let reason = match receipt.validate(&suite_lock_reference_pin(), &suite_lock_corpus_commit()) {
        Err(reason) => reason,
        Ok(()) => panic!(
            "a three-file fixture tree was accepted as a whole-Mathlib observation. The floors are \
             the only thing standing between an empty referent and a row that reads like corpus \
             coverage."
        ),
    };
    assert!(
        reason.contains("closure module(s)") && reason.contains("below the"),
        "the refusal must be about the corpus being too small, not something incidental: {reason}"
    );

    // Serialization does not depend on magnitude: a refused row must still be
    // readable, or a refutation could not be retained and inspected.
    let row = receipt.to_row();
    let parsed = WholeMathlibReceipt::from_row(&row)
        .expect("even a row the guard refuses must survive its own reader");
    assert!(parsed == receipt, "a produced row must round trip");
}

/// The corpus root is EXACTLY the documented host path, compared whole.
///
/// **Why a literal and not the constant.** The path is written out again here by
/// hand. Reusing `DEFAULT_MATHLIB_CORPUS_ROOT` would make this agree with
/// whatever that constant ever held, including a wrong value -- a mirror, not a
/// check. One side is the implementation and this side is the specification, so
/// changing where the lane looks for its corpus has to be done twice, on
/// purpose, and a silent drift fails here.
///
/// **Why equality and not containment.** `contains` would accept
/// `/data/tmp/mathlib4-corpus-old`, `/srv/backup/data/tmp/mathlib4-corpus`, or a
/// path with a trailing separator -- every one of them a different directory,
/// and each would let the lane report on one corpus while the skip row named
/// another.
#[test]
fn the_corpus_root_is_exactly_the_documented_host_path() {
    let root = mathlib_corpus_root();
    match std::env::var_os("FLN_MATHLIB_CORPUS") {
        None => assert_eq!(
            root.as_path(),
            Path::new("/data/tmp/mathlib4-corpus"),
            "with no override the whole-Mathlib lane must look in exactly the documented path; \
             it looked in {}",
            root.display()
        ),
        Some(override_path) => assert_eq!(
            root.as_path(),
            Path::new(&override_path),
            "FLN_MATHLIB_CORPUS must be honoured exactly, with no normalisation of its own"
        ),
    }
    // The override variable's NAME is part of the contract the skip row prints,
    // so it is pinned too.
    assert_eq!(MATHLIB_CORPUS_ROOT_ENV, "FLN_MATHLIB_CORPUS");
}

/// EXISTENCE ALONE decides whether the walk skips.
///
/// **The law.** `classify(root).skips()` is true if and only if `root` is not
/// present on this host. A present root is never skipped: if it identifies
/// itself as the pinned corpus it is walked, and if it cannot it fails. The one
/// outcome that must never happen is a directory sitting on disk while the lane
/// reports a missing host input -- that reads as "nothing to do here" when the
/// truth is "there is something here and it is wrong".
///
/// **Why a table and not one case.** Present-ness has more shapes than
/// "directory": a plain file exists too, and so does a symlink. Each must fall
/// on the not-skipped side, and each takes a different path through the gate, so
/// one example would leave the law asserted for one shape and assumed for the
/// rest. None of these roots is written to or removed; they are read where they
/// already are.
#[test]
fn only_an_absent_root_takes_the_skip_path() {
    let manifest = fln_conformance::checked_manifest_dir!();
    let candidates = [
        (
            "a path that is not on this host",
            PathBuf::from("/data/tmp/fln-t6r7-a-root-that-does-not-exist"),
        ),
        ("a real directory", manifest.clone()),
        ("a real nested directory", manifest.join("tests")),
        (
            "a real file, which is present but not a directory",
            manifest.join("Cargo.toml"),
        ),
    ];

    let mut skipped = 0usize;
    let mut walked_or_failed = 0usize;
    for (description, candidate) in candidates {
        let present = fs::symlink_metadata(&candidate).is_ok();
        let classified = classify_mathlib_corpus_input_at(candidate.clone());
        assert_eq!(
            classified.root(),
            candidate.as_path(),
            "{description}: the classification must be ABOUT the root it was handed"
        );
        assert_eq!(
            classified.skips(),
            !present,
            "{description} ({}): present={present} but skips={}. A root that exists must be \
             walked or refused, never skipped -- a skip claims the input is missing, and this \
             one is not.",
            candidate.display(),
            classified.skips()
        );
        if classified.skips() {
            skipped += 1;
        } else {
            walked_or_failed += 1;
        }
    }

    // ANTI-VACUITY. An `assert_eq!(a, a)`-shaped law holds trivially if every
    // candidate lands on the same side; the table is only a discriminator if
    // both sides are actually populated.
    assert_eq!(
        skipped, 1,
        "exactly one candidate should have been absent; the table no longer discriminates"
    );
    assert_eq!(
        walked_or_failed, 3,
        "three candidates should have been present; the table no longer discriminates"
    );
}

/// The corpus gate's refusals, counted from the function rather than remembered.
///
/// **Seven refusals, one probed.** `preflight_mathlib_corpus_at` can reject an
/// input seven ways. Exactly one -- the commit mismatch -- was ever asserted to
/// fire; a second appeared covered but was only ever named in a NEGATIVE
/// assertion, which says a message is absent and nothing about it being
/// reachable. Counting them from the source rather than from what I remembered
/// writing is what surfaced that, and it is the same correction the conservation
/// laws needed last wave.
///
/// **Three are reachable here and are probed.** A path that is not there, a real
/// file where a directory belongs, and a real directory whose revision is not
/// the pinned one.
///
/// **Four are NOT, and saying which keeps the gap honest.** `cannot inspect
/// corpus checkout` needs `git` to fail to spawn. `is not a readable git
/// checkout` needs a directory outside any repository -- `CARGO_TARGET_TMPDIR`
/// lives under `target/`, which is inside this one, so every fixture path
/// resolves to FrankenLean's HEAD and takes the commit-mismatch branch instead.
/// The last two, about the built Mathlib olean root, are reachable only AFTER
/// the commit check passes, which requires the corpus this bead has never had --
/// they are covered by the same tripwire as the other unexecuted paths.
///
/// **Expectations name what differs.** `must be a real directory` appears in two
/// of the seven, so the cell for the root check asserts the tail unique to it.
#[test]
fn the_corpus_gate_refuses_three_reachable_shapes_distinctly() {
    let manifest = fln_conformance::checked_manifest_dir!();

    let cases = [
        (
            "a root that is not on this host",
            PathBuf::from("/data/tmp/fln-t6r7-a-root-that-does-not-exist"),
            "is unavailable",
        ),
        (
            "a real FILE where a directory belongs",
            manifest.join("Cargo.toml"),
            "not a symlink or non-directory",
        ),
        (
            "a real directory at the wrong revision",
            manifest.clone(),
            "corpus commit",
        ),
    ];

    let mut reasons: Vec<String> = Vec::new();
    for (name, root, expected) in cases {
        let reason = preflight_mathlib_corpus_at(&root)
            .map(|library| {
                panic!("`{name}` was accepted as the pinned corpus, yielding {library:?}")
            })
            .unwrap_err();
        assert!(
            reason.contains(expected),
            "`{name}` was refused, but not for `{expected}`: {reason}"
        );
        reasons.push(reason);
    }

    // THREE SHAPES, THREE DIFFERENT COMPLAINTS. If two collapsed to one message
    // the gate would be refusing them for the same reason, and whoever had to
    // repair a corpus would be told the wrong thing about it.
    let distinct = reasons.iter().collect::<BTreeSet<_>>();
    assert_eq!(
        distinct.len(),
        reasons.len(),
        "the gate gave the same complaint for different inputs: {reasons:?}"
    );
}

/// Three identities are UNIX-ONLY, and off unix they are ABSENT rather than
/// failing.
///
/// **A coverage cliff nothing announced.** The symlinked-file, symlinked-
/// directory and non-UTF-8 refusals each need an input `std::os::unix` alone can
/// construct, so all three carry `#[cfg(unix)]`. On any other platform they do
/// not fail, do not skip, and do not appear: the suite is simply three
/// identities smaller and every run is green. This repository targets Windows
/// too -- `windows_functional_ci.rs` exists -- so that is a live gap, and until
/// now the only record of it was the attribute itself.
///
/// **A vanished test is worse than a skipping one.** Everything else on this
/// bead that cannot run says so in a typed row: the corpus walk when the corpus
/// is absent, the retention guard when no receipt is retained. These three said
/// nothing, because a test that was never compiled has nowhere to say it from.
/// This row is where they say it.
///
/// **The list is bound to the file rather than remembered.** Each name must
/// still exist and must still carry its gate; renaming or ungating one without
/// updating this fails here rather than quietly leaving the row describing tests
/// that are gone. That is the same binding the rejection-class scan uses, and it
/// is cheap: presence, not parsing.
#[test]
fn the_platform_gated_identities_declare_where_they_do_not_run() {
    const GATED: [&str; 3] = [
        "the_inventory_walk_refuses_an_entry_whose_name_is_not_utf8",
        "the_inventory_walk_refuses_a_symlinked_file_entry",
        "the_inventory_walk_refuses_a_symlinked_directory_entry",
    ];
    const SOURCE: &str = include_str!("kernel_replay.rs");

    for name in GATED {
        assert!(
            SOURCE.contains(&format!("fn {name}()")),
            "`{name}` is named here but no longer exists; this row would describe a test that is \
             gone"
        );
        assert!(
            SOURCE.contains(&format!("#[cfg(unix)]\n#[test]\nfn {name}()")),
            "`{name}` is no longer gated as this row claims. If it became portable, remove it \
             from the list; if the gate moved, the row is now describing the wrong thing"
        );
    }

    if cfg!(unix) {
        println!(
            "{{\"schema\":\"fln-t6r7-platform-gated/1\",\"status\":\"active\",\"gated\":{},\
             \"claims\":\"these three identities RAN on this platform\"}}",
            GATED.len()
        );
    } else {
        println!(
            "{{\"schema\":\"fln-t6r7-platform-gated/1\",\"status\":\"absent\",\"gated\":{},\
             \"unverified\":[{}],\
             \"claims\":\"NOTHING about symlinked entries or undecodable names on this platform. \
             The three identities below were not compiled, so a green run here does not cover \
             them.\"}}",
            GATED.len(),
            GATED
                .iter()
                .map(|name| json_string(name))
                .collect::<Vec<_>>()
                .join(",")
        );
    }
}

/// A TRIPWIRE ON A DISCLOSURE, not a check of the product.
///
/// **What is being disclosed.** Two code paths in this file have never executed
/// anywhere: the `Present` arm of `classify_mathlib_corpus_input`, and the
/// `Present` branch of the corpus walk that consumes it. Both are reachable only
/// on a host carrying the pinned Mathlib corpus at
/// `/data/tmp/mathlib4-corpus`, and no host has carried it for the whole life of
/// this bead. Everything I have written about the walk is therefore about its
/// fixture-driven core; the arm that meets a real corpus is unproven.
///
/// **Why this is a test and not a comment.** A disclosure whose producer is the
/// ABSENCE of something rots silently: the corpus lands, the untested paths
/// start running, and nothing anywhere says they were untested until that
/// moment. A comment cannot notice. This can, because provisioning the corpus is
/// exactly the event that makes it fail.
///
/// **When it fails, it is not a defect.** It means the corpus arrived. The right
/// response is to delete this test and read the two `Present` paths carefully,
/// because their first execution will be against 8k modules rather than a
/// three-file fixture. A misprovisioned corpus does NOT trip it -- that is
/// already covered, and the disclosure is specifically about the path taken when
/// the input is genuinely correct.
#[test]
fn the_present_corpus_paths_are_still_unexercised_on_this_host() {
    match classify_mathlib_corpus_input() {
        MathlibCorpusInput::Present { root, library } => panic!(
            "THE CORPUS IS NOW PROVISIONED at {} (library {}), so this tripwire has done its \
             job and should be deleted.\n\n\
             What it was holding open: until this moment the `Present` arm of \
             `classify_mathlib_corpus_input` and the `Present` branch of \
             `the_whole_mathlib_inventory_walks_the_corpus_or_names_what_is_missing` had NEVER \
             executed, on any host, for the whole life of this bead. Every claim made about the \
             walk was about its fixture-driven core.\n\n\
             Those two paths are now live and are running for the first time against a real \
             corpus. Read them before trusting the first green, and expect the inventory to be \
             thousands of modules rather than the three a fixture carries.",
            root.display(),
            library.display()
        ),
        MathlibCorpusInput::Absent { root, .. } => {
            println!(
                "{{\"schema\":\"fln-t6r7-present-path-tripwire/1\",\"status\":\"still_unexercised\",\
                 \"reason\":\"absent\",\"root\":{},\
                 \"claims\":\"NOTHING about the corpus. It records that two Present code paths \
                 have not run.\"}}",
                json_string(&root.display().to_string())
            );
        }
        // A corpus that is present and WRONG leaves the disclosure standing:
        // the untested path is the one taken when the input is correct.
        MathlibCorpusInput::Misprovisioned { root, .. } => {
            println!(
                "{{\"schema\":\"fln-t6r7-present-path-tripwire/1\",\"status\":\"still_unexercised\",\
                 \"reason\":\"misprovisioned\",\"root\":{},\
                 \"claims\":\"NOTHING about the corpus.\"}}",
                json_string(&root.display().to_string())
            );
        }
    }
}

/// The classifier tells ABSENT from MISPROVISIONED, proved on every run.
///
/// **The trap this is here for.** On a host with no corpus the walk above takes
/// its `Absent` arm and asserts nothing whatever about a corpus -- correctly, and
/// that is exactly what makes it decorative. If `classify_mathlib_corpus_input`
/// were broken tomorrow to return `Absent` unconditionally, the walk would keep
/// passing on a machine where the corpus was present and wrong, and the skip row
/// would say "not on this host" about a corpus sitting right there. So the two
/// arms are exercised here against roots chosen so their classification cannot
/// depend on this machine's provisioning.
///
/// **Neither control writes to the filesystem.** They are a path that cannot
/// exist and a directory that certainly does -- this crate's own source tree,
/// which is a real, non-symlinked directory inside a readable git checkout whose
/// `HEAD` is FrankenLean's, never `SUITE.lock`'s corpus commit. That makes it a
/// genuine misprovisioned corpus for classification purposes without anyone
/// having to fabricate one.
#[test]
fn the_corpus_classifier_distinguishes_an_absent_root_from_a_wrong_one() {
    let missing = PathBuf::from("/data/tmp/fln-t6r7-a-root-that-does-not-exist");
    assert!(
        !missing.exists(),
        "the absent-root control must name a path that really is absent"
    );
    match classify_mathlib_corpus_input_at(missing.clone()) {
        MathlibCorpusInput::Absent { root, detail } => {
            assert_eq!(root, missing);
            assert!(
                detail.contains(&*missing.to_string_lossy()),
                "an absent classification must name the path it looked for: {detail}"
            );
        }
        MathlibCorpusInput::Present { .. } => {
            panic!("a nonexistent path was classified as a provisioned corpus")
        }
        MathlibCorpusInput::Misprovisioned { reason, .. } => panic!(
            "a nonexistent path must be ABSENT, not misprovisioned: a missing host input and a \
             wrong one need different responses, and merging them is what this test exists to \
             prevent. Got: {reason}"
        ),
    }

    // A real directory that is emphatically not the pinned Mathlib corpus.
    let present_but_wrong = fln_conformance::checked_manifest_dir!();
    assert!(
        present_but_wrong.is_dir(),
        "the wrong-root control must name a directory that really exists"
    );
    match classify_mathlib_corpus_input_at(present_but_wrong.clone()) {
        MathlibCorpusInput::Misprovisioned { root, reason } => {
            assert_eq!(root, present_but_wrong);
            // NOT MERELY NON-EMPTY. Checking that a reason exists and then never
            // reading it is the shape AGENTS.md records for the discarded
            // no-admission arguments -- a field validated for presence and
            // consumed by nothing. It matters here because this root can be
            // refused for two different KINDS of reason, and only one of them
            // exercises the check this control exists for.
            //
            // An IDENTITY refusal (wrong revision, or not a checkout at all) is
            // the gate doing its job. A SHAPE refusal -- "not a real directory"
            // -- would mean the gate misread a real directory as something else,
            // and the control would be passing while testing nothing about
            // corpus identity. Both identity spellings are accepted because a
            // git-less export legitimately produces the second.
            assert!(
                reason.contains("corpus commit") || reason.contains("readable git checkout"),
                "the refusal must be about this root's IDENTITY as a corpus, not something \
                 incidental: {reason}"
            );
            // `must be a real directory` appears in TWO of preflight's messages --
            // the corpus root's and the built-Mathlib root's -- so the tail
            // unique to the root check is what this must name.
            assert!(
                !reason.contains("not a symlink or non-directory"),
                "a real directory was refused for not being one, so the gate misread its input \
                 and this control is not exercising the corpus-identity check: {reason}"
            );
        }
        MathlibCorpusInput::Absent { .. } => panic!(
            "a directory that exists was classified as ABSENT. This is the failure the walk \
             cannot see for itself: it would skip, report a missing host input, and be wrong \
             about a corpus that was right there"
        ),
        MathlibCorpusInput::Present { .. } => panic!(
            "this crate's source tree was accepted as the pinned Mathlib corpus; the gate is \
             not checking the corpus commit at all"
        ),
    }
}

/// The present-olean inventory walk over the whole-Mathlib corpus -- reachable
/// by default, which is the whole point of it (bead `franken_lean-t6r7`).
///
/// **Why another one when two already exist.** `whole_mathlib_corpus_resurrection_preflight`
/// and `_sweep` both cover this ground and both are `#[ignore]`d, so an ordinary
/// `cargo test` says NOTHING about whether the corpus input is present, absent
/// or wrong. The state of that input is the single fact this bead has been
/// blocked on since 2026-08-04, and until now it was discoverable only by
/// someone remembering to run an ignored test by name. This one runs in the
/// batch and reports the input's state in a typed row every time.
///
/// **THE EXACT MISSING HOST INPUT**, so the skip below names something
/// actionable rather than "not available":
///
///   path:    `/data/tmp/mathlib4-corpus` (override with `FLN_MATHLIB_CORPUS`)
///   shape:   a real directory, NOT a symlink, holding a git checkout whose
///            `HEAD` is `SUITE.lock`'s `corpus commit=` field, with built
///            oleans under `.lake/build/lib/lean/Mathlib`
///   size:    at least `WHOLE_MATHLIB_SEED_FLOOR` modules; a truncated corpus is
///            not a smaller green walk
///
/// **What this walk is, and what it is NOT.** It enumerates the built olean set
/// and derives canonical module names from it. It DOES NOT DECODE ANYTHING, does
/// not build an import closure, does not reach the kernel and does not involve
/// the oracle. The decode walk is the `#[ignore]`d `_sweep` (826 s when it last
/// ran) and the differential is hours-class; making either reachable by default
/// would put that cost on every commit. Inventory is the part that is cheap
/// enough to be free, and it is the part that answers "is the input there".
#[test]
fn the_whole_mathlib_inventory_walks_the_corpus_or_names_what_is_missing() {
    match classify_mathlib_corpus_input() {
        MathlibCorpusInput::Absent { root, detail } => {
            // THE SKIP'S IDENTITY IS EXACT. This was a substring containment on
            // the human-readable detail, which is far too loose to be an
            // identity: `/data/tmp/mathlib4-corpus-old`, a stale sibling, or any
            // path merely CONTAINING the required one would have satisfied it,
            // and the row would then disclose a missing input while naming the
            // wrong file. The path is compared whole, against the documented
            // requirement rather than against itself.
            assert_eq!(
                root.as_path(),
                mathlib_corpus_root().as_path(),
                "the skip must be about the root the lane actually requires"
            );
            assert!(
                !detail.trim().is_empty(),
                "a skip with an empty detail is a green that reports nothing"
            );
            println!(
                "{{\"schema\":\"fln-t6r7-mathlib-inventory/1\",\"status\":\"skipped_absent_host_input\",\
                 \"required_path\":{},\"override_env\":\"FLN_MATHLIB_CORPUS\",\
                 \"required_corpus_commit\":{},\"required_library_subpath\":\".lake/build/lib/lean/Mathlib\",\
                 \"required_min_modules\":{},\"detail\":{},\
                 \"claims\":\"NOTHING. The corpus is not on this host, so no module was enumerated, \
                 nothing was decoded, and no kernel or oracle verdict exists. This row records a \
                 missing input, never a clean walk.\"}}",
                json_string(&root.display().to_string()),
                json_string(&suite_lock_corpus_commit()),
                WHOLE_MATHLIB_SEED_FLOOR,
                json_string(&detail),
            );
        }
        MathlibCorpusInput::Misprovisioned { root, reason } => {
            // NOT a skip. The input is present and is the wrong thing, and a
            // green here would certify the wrong corpus.
            panic!(
                "the whole-Mathlib corpus root {} exists but is not the pinned corpus: {reason}. \
                 This is a misprovisioned input, not a missing one, so it fails rather than \
                 skipping -- a walk over another Mathlib revision would be evidence about \
                 another world.",
                root.display()
            );
        }
        MathlibCorpusInput::Present { root, library } => {
            // The tree-shape properties are checked by `walk_olean_inventory`,
            // which a fixture also drives, so they are reachable without the
            // corpus. Only the SIZE floor is corpus-specific and stays here.
            let OleanInventory { oleans, modules } =
                walk_olean_inventory(&library, Some("Mathlib")).unwrap_or_else(|reason| {
                    panic!("the built whole-Mathlib olean tree is not walkable: {reason}")
                });
            assert!(
                modules.len() as u64 >= WHOLE_MATHLIB_SEED_FLOOR,
                "the whole-Mathlib inventory found only {} module(s) under {}; a truncated \
                 corpus is not a smaller green walk",
                modules.len(),
                library.display()
            );
            let paths = oleans;

            println!(
                "{{\"schema\":\"fln-t6r7-mathlib-inventory/1\",\"status\":\"walked\",\
                 \"root\":{},\"library\":{},\"corpus_commit\":{},\"oleans\":{},\"modules\":{},\
                 \"decoded\":0,\
                 \"claims\":\"INVENTORY ONLY. The built olean set was enumerated and projected to \
                 canonical module names. Nothing was decoded, no import closure was built, no \
                 declaration reached the kernel and the oracle was not consulted. This is not a \
                 differential, not G1 and not PG-1.\"}}",
                json_string(&root.display().to_string()),
                json_string(&library.display().to_string()),
                json_string(&suite_lock_corpus_commit()),
                paths.len(),
                modules.len(),
            );
        }
    }
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
                paths.len() as u64 >= WHOLE_MATHLIB_SEED_FLOOR,
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
        mathlib_modules.len() as u64 >= WHOLE_MATHLIB_SEED_FLOOR,
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

/// The coverage floors the whole-Mathlib lane refuses to publish below, named
/// once so the producer and the receipt reader cannot drift apart. The receipt
/// guard re-derives its anti-vacuity floors from these same constants: a row
/// recording fewer modules than the driver asserts before it compares anything
/// could not have come from a run of this lane.
const WHOLE_MATHLIB_MODULE_FLOOR: u64 = 10_000;
const WHOLE_MATHLIB_DECODED_FLOOR: u64 = 700_000;
/// The floor on `Mathlib.*` SEED modules, as distinct from the closure they pull
/// in. The pinned corpus provisions ~8.2k of them; the closure adds `Init`,
/// `Std`, `Lean` and the package tree on top, which is why the two floors differ
/// by thousands and why a row must carry both numbers.
const WHOLE_MATHLIB_SEED_FLOOR: u64 = 8_000;

const WHOLE_MATHLIB_RECEIPT_SCHEMA: &str = "fln.whole-mathlib-differential-receipt/1";

/// The retained receipt for one whole-Mathlib differential run (bead
/// `franken_lean-t6r7`, mirroring `franken_lean-p6x1`'s corpus-matrix receipt).
///
/// **Why a receipt at all.** The lane is hours-class and on demand, so what it
/// observed exists only in a terminal unless something writes it down. A month
/// later "the whole-Mathlib differential was clean" would rest on a memory, and
/// a memory cannot be distinguished from a run that never happened. The row
/// binds the three things that decide whether the observation is about *this*
/// world: the Reference pin, the corpus revision (`corpus_commit` from
/// `SUITE.lock` plus `corpus_fixture_hash`, the inventory's own hash over every
/// module and its bytes), and the host it ran on.
///
/// **Why the file is keyed by pin.** The receipt lives at
/// `evidence/whole_mathlib_differential/<pin>.jsonl`, so the path itself carries
/// the binding: when `SUITE.lock` advances the Reference, the file for the new
/// epoch does not exist and any future retention guard fails without anyone
/// having to remember a date or read a clock.
///
/// **What the row is NOT.** It is one bounded observation at one pin, corpus
/// revision, host and build — class `bounded_model`, never an invariant, and
/// never a G1 or PG-1 claim. Whole-corpus acceptance is not claimed anywhere
/// today and a green row here does not begin to claim it: `unscorable` is
/// carried in the row precisely so that a run which compared a fraction of the
/// corpus cannot be quoted as a run over the corpus.
///
/// **The triage is part of the format.** `restrictive_families` and
/// `no_answer_families` carry the per-family census, and [`Self::validate`]
/// refuses a row whose families do not sum to the buckets they describe. A
/// partial triage therefore cannot be filed as a complete one — which is the
/// whole content of "triage every rejection to a named family".
#[derive(Clone, PartialEq, Eq)]
struct WholeMathlibReceipt {
    bead: String,
    pin: String,
    corpus_commit: String,
    observed_unix_s: u64,
    corpus_fixture_hash: String,
    /// Modules in the replayed import CLOSURE. For the whole-Mathlib lane this
    /// is strictly larger than `seed_modules`: it includes every `Init`, `Std`,
    /// `Lean` and package module Mathlib imports. It was called `modules` for
    /// exactly one commit, which invited the reading "the Mathlib corpus is this
    /// big" -- a number about the closure wearing the name of the corpus.
    closure_modules: u64,
    /// Modules the lane SEEDED, i.e. the `Mathlib.*` population the phrase
    /// "whole Mathlib" actually refers to. Carried so that claim is
    /// substantiated by the row rather than implied by the lane's name.
    seed_modules: u64,
    decoded: u64,
    compared: u64,
    agree: u64,
    unsoundly_permissive: u64,
    restrictive_with_carve_out: u64,
    restrictive_without_carve_out: u64,
    unscorable: u64,
    oracle_skipped: u64,
    subject_no_answer: u64,
    restrictive_families: Vec<String>,
    no_answer_families: Vec<String>,
    wall_ms: u64,
    profile: String,
    target: String,
    available_parallelism: u64,
    lane_source_digest_at_run: String,
    class: String,
}

/// The class token a run earns, derived from what it actually observed rather
/// than chosen by whoever files the row.
///
/// **One statement, two callers, on purpose.** The producer calls this to fill
/// the row in and [`WholeMathlibReceipt::validate`] calls it to decide whether
/// the row it is reading told the truth. Writing the rule twice -- once as an
/// `if` chain here and once as a `match` there -- would look like independent
/// corroboration and be nothing of the kind: the two copies can drift, and the
/// drift is silent in the direction that matters. A producer whose rule had
/// grown a case the validator lacked would file rows its own guard rejects; a
/// validator whose rule lagged the producer's would wave through exactly the
/// refutation-wearing-the-clean-class this token exists to prevent. This
/// function takes the two counts rather than a `CorpusCounts` so the reader,
/// which has only the parsed row, can call the same code the writer did.
fn whole_mathlib_class(
    unsoundly_permissive: u64,
    restrictive_without_carve_out: u64,
) -> &'static str {
    if unsoundly_permissive != 0 {
        // Accepting what the Reference rejects is release-blocking. It must not
        // sit quietly in an evidence file wearing the clean class.
        "refuted_this_run_accepted_what_the_reference_rejected"
    } else if restrictive_without_carve_out != 0 {
        "refuted_this_run_found_a_restrictive_divergence"
    } else {
        "observed_once_not_an_invariant"
    }
}

/// Everything a receipt needs that the RUN produces, separated from everything
/// it needs that the HOST produces.
///
/// The split exists so the field mapping can be tested. Built inline, the
/// producer was a 25-field struct literal that nothing exercised: a
/// transposition -- `agree: total.compared`, `oracle_skipped:
/// total.subject_no_answer` -- would compile, satisfy every conservation law
/// that happened to still balance, and file a plausible row. The lane that would
/// have caught it needs a corpus that is not on this host, so the only way to
/// check the mapping is to make it a function of its inputs and hand it inputs.
struct WholeMathlibRunFacts<'a> {
    spec: &'a CorpusReceiptSpec,
    counts: &'a CorpusCounts,
    closure_modules: u64,
    corpus_fixture_hash: &'a str,
    observed_unix_s: u64,
    wall_ms: u64,
}

impl WholeMathlibReceipt {
    /// Assemble a receipt from one run's facts. Pure in its arguments except for
    /// the four ambient host descriptors, which are properties of the machine
    /// rather than of the observation and are read here so an operator cannot
    /// forget or mistype them.
    fn from_run(facts: &WholeMathlibRunFacts<'_>) -> WholeMathlibReceipt {
        let counts = facts.counts;
        WholeMathlibReceipt {
            bead: facts.spec.bead.to_string(),
            pin: suite_lock_reference_pin(),
            corpus_commit: facts.spec.corpus_commit.clone(),
            observed_unix_s: facts.observed_unix_s,
            corpus_fixture_hash: facts.corpus_fixture_hash.to_string(),
            closure_modules: facts.closure_modules,
            seed_modules: facts.spec.seed_modules,
            decoded: counts.decoded,
            compared: counts.compared,
            agree: counts.agree,
            unsoundly_permissive: counts.unsoundly_permissive,
            restrictive_with_carve_out: counts.restrictive_with_carve_out,
            restrictive_without_carve_out: counts.restrictive_without_carve_out,
            unscorable: counts.unscorable,
            oracle_skipped: counts.oracle_skipped,
            subject_no_answer: counts.subject_no_answer,
            restrictive_families: family_census_rows(&counts.restrictive_families),
            no_answer_families: family_census_rows(&counts.no_answer_families),
            wall_ms: facts.wall_ms,
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
            // The lane digests its OWN source, so the provenance cannot be
            // forgotten by an operator or mistyped by one.
            lane_source_digest_at_run: hash(
                Domain::Fixture,
                include_str!("kernel_replay.rs").as_bytes(),
            )
            .to_hex(),
            class: whole_mathlib_class(
                counts.unsoundly_permissive,
                counts.restrictive_without_carve_out,
            )
            .to_string(),
        }
    }

    /// The canonical one-line form. Field order is fixed and is part of the
    /// format: a receipt that does not re-serialize to the bytes it was read
    /// from is refused rather than repaired, so there is exactly one spelling
    /// of a given observation.
    fn to_row(&self) -> String {
        let strings = |values: &[String]| {
            values
                .iter()
                .map(|value| json_string(value))
                .collect::<Vec<_>>()
                .join(",")
        };
        format!(
            "{{\"schema\":{},\"bead\":{},\"pin\":{},\"corpus_commit\":{},\
             \"observed_unix_s\":{},\"corpus_fixture_hash\":{},\"closure_modules\":{},\
             \"seed_modules\":{},\"decoded\":{},\"compared\":{},\"agree\":{},\"unsoundly_permissive\":{},\
             \"restrictive_with_carve_out\":{},\"restrictive_without_carve_out\":{},\
             \"unscorable\":{},\"oracle_skipped\":{},\"subject_no_answer\":{},\
             \"restrictive_families\":[{}],\"no_answer_families\":[{}],\"wall_ms\":{},\
             \"profile\":{},\"target\":{},\"available_parallelism\":{},\
             \"lane_source_digest_at_run\":{},\"class\":{}}}",
            json_string(WHOLE_MATHLIB_RECEIPT_SCHEMA),
            json_string(&self.bead),
            json_string(&self.pin),
            json_string(&self.corpus_commit),
            self.observed_unix_s,
            json_string(&self.corpus_fixture_hash),
            self.closure_modules,
            self.seed_modules,
            self.decoded,
            self.compared,
            self.agree,
            self.unsoundly_permissive,
            self.restrictive_with_carve_out,
            self.restrictive_without_carve_out,
            self.unscorable,
            self.oracle_skipped,
            self.subject_no_answer,
            strings(&self.restrictive_families),
            strings(&self.no_answer_families),
            self.wall_ms,
            json_string(&self.profile),
            json_string(&self.target),
            self.available_parallelism,
            json_string(&self.lane_source_digest_at_run),
            json_string(&self.class),
        )
    }

    /// Read a row, then prove the read was faithful by re-serializing it.
    ///
    /// Extraction is by key and so tolerant of order; the round-trip is what
    /// makes the format strict. A parser that silently accepted a row it could
    /// not reproduce would let a guard check a value nobody wrote.
    fn from_row(row: &str) -> Result<WholeMathlibReceipt, String> {
        fn text(row: &str, key: &str) -> Result<String, String> {
            let needle = format!("\"{key}\":\"");
            assert_field_once(row, key, &needle)?;
            let start = row
                .find(&needle)
                .ok_or_else(|| format!("missing string field `{key}`"))?
                + needle.len();
            let rest = &row[start..];
            let end = rest
                .find('"')
                .ok_or_else(|| format!("unterminated string field `{key}`"))?;
            let value = &rest[..end];
            assert_no_escape(key, value)?;
            assert_string_terminator(key, rest, end)?;
            Ok(value.to_string())
        }
        fn number(row: &str, key: &str) -> Result<u64, String> {
            let needle = format!("\"{key}\":");
            assert_field_once(row, key, &needle)?;
            let start = row
                .find(&needle)
                .ok_or_else(|| format!("missing numeric field `{key}`"))?
                + needle.len();
            let rest = &row[start..];
            let end = rest
                .find(|c: char| !c.is_ascii_digit())
                .unwrap_or(rest.len());
            assert_number_terminator(key, rest, end)?;
            rest[..end]
                .parse()
                .map_err(|_| format!("field `{key}` is not a u64"))
        }
        fn strings(row: &str, key: &str) -> Result<Vec<String>, String> {
            let needle = format!("\"{key}\":[");
            assert_field_once(row, key, &needle)?;
            let start = row
                .find(&needle)
                .ok_or_else(|| format!("missing array field `{key}`"))?
                + needle.len();
            let rest = &row[start..];
            let end = rest
                .find(']')
                .ok_or_else(|| format!("unterminated array field `{key}`"))?;
            assert_array_terminator(key, rest, end)?;
            let items = rest[..end]
                .split(',')
                .filter(|item| !item.is_empty())
                .collect::<Vec<_>>();
            for item in &items {
                assert_whole_quoted_element(key, item)?;
            }
            Ok(items
                .iter()
                .map(|item| item.trim_matches('"').to_string())
                .collect())
        }
        let schema = text(row, "schema")?;
        if schema != WHOLE_MATHLIB_RECEIPT_SCHEMA {
            return Err(format!(
                "receipt schema is `{schema}`, expected `{WHOLE_MATHLIB_RECEIPT_SCHEMA}`"
            ));
        }
        let receipt = WholeMathlibReceipt {
            bead: text(row, "bead")?,
            pin: text(row, "pin")?,
            corpus_commit: text(row, "corpus_commit")?,
            observed_unix_s: number(row, "observed_unix_s")?,
            corpus_fixture_hash: text(row, "corpus_fixture_hash")?,
            closure_modules: number(row, "closure_modules")?,
            seed_modules: number(row, "seed_modules")?,
            decoded: number(row, "decoded")?,
            compared: number(row, "compared")?,
            agree: number(row, "agree")?,
            unsoundly_permissive: number(row, "unsoundly_permissive")?,
            restrictive_with_carve_out: number(row, "restrictive_with_carve_out")?,
            restrictive_without_carve_out: number(row, "restrictive_without_carve_out")?,
            unscorable: number(row, "unscorable")?,
            oracle_skipped: number(row, "oracle_skipped")?,
            subject_no_answer: number(row, "subject_no_answer")?,
            restrictive_families: strings(row, "restrictive_families")?,
            no_answer_families: strings(row, "no_answer_families")?,
            wall_ms: number(row, "wall_ms")?,
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

    /// Sum a `token=count` family census back to the number of rows it triages.
    fn family_total(rows: &[String], direction: FamilyDirection) -> Result<u64, String> {
        let field = direction.field();
        let mut total = 0u64;
        let mut seen = BTreeSet::new();
        let mut previous: Option<&str> = None;
        for entry in rows {
            let (family, count) = entry
                .rsplit_once('=')
                .ok_or_else(|| format!("`{field}` entry `{entry}` is not `family=count`"))?;
            check_family_token(family, direction)?;
            // ASCENDING, BECAUSE THE FORMAT SAYS SO. The census is rendered in
            // `BTreeMap` order precisely so two runs that saw the same families
            // produce byte-identical rows. The producer sorted; nothing here
            // required it, so a retained row could carry the same census in any
            // order and validate -- and byte-identity would quietly be a
            // property of the producer alone, while any consumer comparing two
            // retained rows would see a difference that is not one.
            if let Some(previous) = previous
                && family < previous
            {
                return Err(format!(
                    "`{field}` lists `{family}` after `{previous}`, so the census is not in \
                     ascending order. Two runs that saw the same families must produce the same \
                     bytes, and this row would compare unequal to one describing the same run"
                ));
            }
            previous = Some(family);
            if !seen.insert(family.to_string()) {
                return Err(format!(
                    "`{field}` names family `{family}` twice; the census would double-count it"
                ));
            }
            let parsed = count
                .parse::<u64>()
                .map_err(|_| format!("`{field}` entry `{entry}` has a non-u64 count"))?;
            if parsed == 0 {
                return Err(format!(
                    "`{field}` entry `{entry}` counts zero rows; an empty family is not a triage"
                ));
            }
            total = checked_sum(field, &[total, parsed])?;
        }
        Ok(total)
    }

    /// Everything the row must say to be evidence for a sentence that cites it.
    ///
    /// **Why a function and not assertions at one call site.** It has two
    /// callers: the mutant test below, which runs it over forged rows, and any
    /// future retention guard, which will run it over a committed file. A second
    /// copy of these rules written for the test could drift from the one that
    /// gates, and the mutants would then prove a check that no longer runs.
    ///
    /// **What it is for.** The failure mode this is built against is the
    /// empty-referent row: `modules: 0, decoded: 0, compared: 0` satisfies
    /// "zero divergences" perfectly and would stand as the retained evidence for
    /// a whole-corpus observation. Size and conservation are checked BEFORE
    /// content for exactly that reason. The floors are `>=`: a larger corpus is
    /// not a failure, a smaller one is.
    fn validate(&self, pin: &str, corpus_commit: &str) -> Result<(), String> {
        if self.pin != pin {
            return Err(format!(
                "row records pin {} but the file is the {pin} epoch's. The path IS the \
                 binding; a row filed under the wrong epoch would make the guard check an \
                 observation of another Reference",
                self.pin
            ));
        }
        if self.corpus_commit != corpus_commit {
            return Err(format!(
                "row records corpus commit {} but SUITE.lock pins {corpus_commit}. A complete \
                 run over a DIFFERENT Mathlib revision is evidence about another corpus",
                self.corpus_commit
            ));
        }

        // ANTI-VACUITY, before any content check. `all()` over an empty
        // population is vacuously true, and so is "no divergences" over no
        // comparisons.
        if self.closure_modules < WHOLE_MATHLIB_MODULE_FLOOR {
            return Err(format!(
                "row records {} closure module(s), below the {WHOLE_MATHLIB_MODULE_FLOOR} the \
                 driver asserts before it compares anything. Zero divergences over a corpus \
                 this small is not the observation the row appears to carry",
                self.closure_modules
            ));
        }
        if self.seed_modules < WHOLE_MATHLIB_SEED_FLOOR {
            return Err(format!(
                "row records {} seeded Mathlib module(s), below the {WHOLE_MATHLIB_SEED_FLOOR} \
                 floor. A large CLOSURE around a truncated seed set is still not whole Mathlib, \
                 and this is the cell that separates the two",
                self.seed_modules
            ));
        }
        if self.seed_modules > self.closure_modules {
            return Err(format!(
                "row records {} seed module(s) inside a {} module closure; a seed set cannot \
                 exceed the closure that contains it and the row contradicts itself",
                self.seed_modules, self.closure_modules
            ));
        }
        if self.decoded < WHOLE_MATHLIB_DECODED_FLOOR {
            return Err(format!(
                "row records {} decoded declaration(s), below the {WHOLE_MATHLIB_DECODED_FLOOR} \
                 floor",
                self.decoded
            ));
        }
        if self.compared == 0 {
            return Err(
                "row records zero declarations compared. `restrictive_without_carve_out: 0` \
                 over zero comparisons is not agreement; it is the absence of a measurement \
                 wearing the shape of one"
                    .to_string(),
            );
        }
        if self.observed_unix_s == 0 {
            return Err(
                "row records observed_unix_s: 0. A receipt with no observation instant cannot \
                 date the evidence it carries. The producer sets this from the clock at the \
                 end of the run, so zero means the row was constructed rather than observed"
                    .to_string(),
            );
        }
        if self.wall_ms == 0 {
            return Err(
                "row records wall_ms: 0. The whole Mathlib closure does not decode, replay and \
                 score in under a millisecond, and this number is the priced input to the \
                 cadence decision that keeps the lane on demand"
                    .to_string(),
            );
        }

        // CONSERVATION. The producer asserts these live; the row re-states them
        // so a hand-edited file cannot quietly contradict the run it claims.
        let population = checked_sum("compared + unscorable", &[self.compared, self.unscorable])?;
        if self.decoded != population {
            return Err(format!(
                "row does not conserve its own population: decoded {} != compared {} + \
                 unscorable {}",
                self.decoded, self.compared, self.unscorable
            ));
        }
        let buckets = checked_sum(
            "the D23 direction buckets",
            &[
                self.agree,
                self.unsoundly_permissive,
                self.restrictive_with_carve_out,
                self.restrictive_without_carve_out,
            ],
        )?;
        if self.compared != buckets {
            return Err(format!(
                "row does not conserve the D23 direction buckets: compared {} != {buckets}",
                self.compared
            ));
        }
        let unscorable_split = checked_sum(
            "the unscorable split",
            &[self.oracle_skipped, self.subject_no_answer],
        )?;
        if self.unscorable != unscorable_split {
            return Err(format!(
                "row does not split its unscorable population: unscorable {} != oracle_skipped \
                 {} + subject_no_answer {}. This is the only law that binds oracle_skipped at \
                 all; without it the field is free and the row could say anything about how \
                 much the oracle declined to answer for",
                self.unscorable, self.oracle_skipped, self.subject_no_answer
            ));
        }

        // THE TRIAGE IS TOTAL. A row may not claim a family census that covers
        // fewer rows than the buckets it describes.
        let restrictive =
            Self::family_total(&self.restrictive_families, FamilyDirection::Restrictive)?;
        let restrictive_rows = checked_sum(
            "the restrictive comparisons",
            &[
                self.restrictive_with_carve_out,
                self.restrictive_without_carve_out,
            ],
        )?;
        if restrictive != restrictive_rows {
            return Err(format!(
                "restrictive_families triages {restrictive} row(s) but the row records {} \
                 restrictive comparison(s); a partial triage must not be filed as a complete one",
                restrictive_rows
            ));
        }
        let no_answer = Self::family_total(&self.no_answer_families, FamilyDirection::NoAnswer)?;
        if no_answer != self.subject_no_answer {
            return Err(format!(
                "no_answer_families triages {no_answer} row(s) but the row records {} subject \
                 non-answer(s)",
                self.subject_no_answer
            ));
        }

        // PROVENANCE. Empty strings are not weak provenance, they are none.
        // TRIMMED, LIKE `bead` AND `target` TWO RULES DOWN. This was
        // `is_empty()`, so a hash of spaces named no corpus revision and passed
        // anyway -- the exact thing the message below says it refuses. A
        // retained row is editable by hand, which is why this file already
        // refuses to trust its numbers into arithmetic; a blank field is the
        // same threat wearing a different shape.
        if self.corpus_fixture_hash.trim().is_empty() {
            return Err(
                "row carries an empty corpus_fixture_hash, so it names no corpus revision"
                    .to_string(),
            );
        }
        if self.lane_source_digest_at_run.trim().is_empty() {
            return Err(
                "row carries an empty lane_source_digest_at_run, so it names no producing source"
                    .to_string(),
            );
        }
        if self.bead.trim().is_empty() {
            return Err(
                "row carries an empty bead, so a retained observation names no work item and \
                 cannot be routed to whoever owns it"
                    .to_string(),
            );
        }
        // PROFILE IS NOT DECORATION: it is what makes `wall_ms` mean anything.
        // That number is the priced input to the cadence decision that keeps
        // this lane on demand, and the same corpus takes roughly an order of
        // magnitude longer under `dev` than under `release`. A row that
        // mislabels which one it ran under misprices exactly the decision the
        // receipt exists to inform, while every other field stays true. The
        // producer can only emit these two, so a third value was not produced by
        // a run.
        if self.profile != "dev" && self.profile != "release" {
            return Err(format!(
                "row records profile `{}`, but the producer emits only `dev` or `release`. \
                 `wall_ms` is uninterpretable without knowing which, and it is the number the \
                 cadence decision rests on",
                self.profile
            ));
        }
        if self.target.trim().is_empty() {
            return Err(
                "row carries an empty target, so it names no host architecture and its timing \
                 cannot be compared with any other row's"
                    .to_string(),
            );
        }
        // `available_parallelism` is DELIBERATELY unconstrained, stated here so
        // the asymmetry above is a decision rather than an oversight: the
        // producer writes 0 when the host would not report it, so zero is a
        // legitimate value meaning "unknown" and refusing it would refuse honest
        // rows from hosts that cannot answer.

        // CONTENT. The class must match what the counts actually say: a
        // refutation wearing the clean token is the one failure this format
        // exists to make impossible.
        let expected = whole_mathlib_class(
            self.unsoundly_permissive,
            self.restrictive_without_carve_out,
        );
        if self.class != expected {
            return Err(format!(
                "row claims class {} but its own counts earn {expected} \
                 (unsoundly_permissive={}, restrictive_without_carve_out={})",
                self.class, self.unsoundly_permissive, self.restrictive_without_carve_out
            ));
        }
        Ok(())
    }
}

/// Where the retained whole-Mathlib receipts for a given Reference pin live.
///
/// **No retention guard exists yet, deliberately.** The corpus this lane needs
/// is host state that is NOT provisioned on this machine today, so no run can
/// have produced a row, so a guard demanding a committed receipt would be a
/// standing red for the absence of an input rather than for a defect. The
/// binding this path expresses becomes enforceable the first time the lane runs
/// against a provisioned corpus and its row is committed.
fn whole_mathlib_receipt_path(pin: &str) -> PathBuf {
    // THE PIN IS INTERPOLATED INTO A PATH, SO IT HAS TO BE ABLE TO NAME A FILE.
    // `join` obeys the string it is given: a pin carrying a separator nests the
    // receipt into a subdirectory, and one carrying `..` leaves the evidence
    // directory altogether. Measured, both.
    //
    // The neighbouring test already requires two epochs not to share a receipt
    // file, and checks it by comparing two PATHS. That is a lexical test of a
    // filesystem claim: `v1/../v2` and `v2` compare unequal and resolve to the
    // same file, so the assertion passes while the property fails.
    let mut components = Path::new(pin).components();
    let single = matches!(
        components.next(),
        Some(std::path::Component::Normal(name)) if name == std::ffi::OsStr::new(pin)
    ) && components.next().is_none();
    assert!(
        single,
        "Reference pin `{pin}` is not a single ordinary path component, so it cannot name a \
         receipt file. A pin with a separator nests the file and one with `..` leaves the \
         evidence directory; two such pins can resolve to one file while their paths compare \
         unequal"
    );
    fln_conformance::checked_manifest_dir!()
        .join("evidence/whole_mathlib_differential")
        .join(format!("{pin}.jsonl"))
}

/// Read `RejectClass`'s variants out of the kernel's own source.
///
/// The list in the test below is written by hand -- there is no way to enumerate
/// a Rust enum at runtime -- so something has to prove that list is COMPLETE.
/// This does, and it is also where a payload variant is caught: `Debug` renders
/// `Foo { a: 1, b: 2 }`, whose commas would split one census entry into several
/// and whose braces would be re-read as part of a family name.
fn reject_class_variants_from_source() -> BTreeSet<String> {
    const SOURCE: &str = include_str!("../../fln-kernel/src/verdict.rs");
    let start = SOURCE
        .find("pub enum RejectClass {")
        .expect("fln-kernel must still declare `pub enum RejectClass`");
    let body = &SOURCE[start..];
    let end = body
        .find("\n}")
        .expect("the RejectClass declaration must terminate");
    let mut variants = BTreeSet::new();
    for line in body[..end].lines().skip(1) {
        let line = line.trim();
        if line.is_empty() || line.starts_with("//") {
            continue;
        }
        assert!(
            !line.contains('(') && !line.contains('{'),
            "RejectClass variant `{line}` carries a payload. Its `Debug` rendering embeds the \
             field list, whose commas and braces are delimiters in the whole-Mathlib receipt's \
             family census: one entry would be re-read as several, under names nobody wrote. \
             Give the variant no payload, or teach the census format to escape one."
        );
        let name = line.trim_end_matches(',').trim();
        assert!(
            !name.is_empty() && name.chars().all(|c| c.is_ascii_alphanumeric()),
            "unexpected syntax in the RejectClass declaration: `{line}`"
        );
        variants.insert(name.to_string());
    }
    variants
}

/// Every rejection class the kernel can actually produce must yield a family
/// token this format can carry, and must be refused on the other side of the
/// census.
///
/// **Three mechanisms, because each catches what the others miss.** The `match`
/// is exhaustive with no wildcard, so adding a variant STOPS THE BUILD until
/// someone looks at this. The source scan proves the hand-written array is
/// complete, since a new arm could otherwise be added to the match while the
/// array kept the old population. And the token check is run against the real
/// `Debug` rendering rather than against the parsed name, so it tests the string
/// the lane would actually put in a row.
#[test]
fn every_kernel_rejection_class_yields_a_legal_family_token() {
    use fln_kernel::verdict::RejectClass;

    let all = [
        RejectClass::LooseBVar,
        RejectClass::MVarInKernel,
        RejectClass::UnknownFVar,
        RejectClass::UnknownConstant,
        RejectClass::UniverseArityMismatch,
        RejectClass::UndefinedLevelParam,
        RejectClass::FunctionExpected,
        RejectClass::TypeMismatch,
        RejectClass::SortExpected,
        RejectClass::InvalidProjection,
        RejectClass::AlreadyDeclared,
        RejectClass::DuplicateLevelParams,
        RejectClass::TheoremNotProp,
        RejectClass::DefinitionTypeMismatch,
        RejectClass::NotDefEq,
        RejectClass::SafetyViolation,
        RejectClass::BlockMismatch,
    ];

    // COMPILE-TIME COMPLETENESS. No wildcard, so a new variant is a build error
    // here rather than a family token nobody checked.
    for class in all {
        match class {
            RejectClass::LooseBVar
            | RejectClass::MVarInKernel
            | RejectClass::UnknownFVar
            | RejectClass::UnknownConstant
            | RejectClass::UniverseArityMismatch
            | RejectClass::UndefinedLevelParam
            | RejectClass::FunctionExpected
            | RejectClass::TypeMismatch
            | RejectClass::SortExpected
            | RejectClass::InvalidProjection
            | RejectClass::AlreadyDeclared
            | RejectClass::DuplicateLevelParams
            | RejectClass::TheoremNotProp
            | RejectClass::DefinitionTypeMismatch
            | RejectClass::NotDefEq
            | RejectClass::SafetyViolation
            | RejectClass::BlockMismatch => {}
        }
    }

    // RUNTIME COMPLETENESS. Binds the array above to the kernel's declaration,
    // so the array cannot quietly describe a smaller enum than the one that
    // exists.
    let listed = all
        .iter()
        .map(|class| format!("{class:?}"))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        listed.len(),
        all.len(),
        "two entries of the array render to the same Debug string"
    );
    let declared = reject_class_variants_from_source();
    assert!(
        declared.len() >= 17,
        "the RejectClass scan found only {} variant(s); a scan that parsed nothing would make \
         every check below vacuous",
        declared.len()
    );
    assert_eq!(
        listed, declared,
        "the rejection classes listed in this test have drifted from the kernel's enum"
    );
    // The two families this bead's own history is made of, named so a rename
    // upstream cannot silently empty the check.
    assert!(declared.contains("BlockMismatch") && declared.contains("DefinitionTypeMismatch"));

    for name in &declared {
        let token = format!("rejected:{name}");
        if let Err(reason) = check_family_token(&token, FamilyDirection::Restrictive) {
            panic!("the kernel can reject with `{name}`, but `{token}`: {reason}");
        }
        assert_family_token_refused(&token, FamilyDirection::NoAnswer, "is a `rejected:` token");
    }

    // And the two context families the scorer writes, from the other direction.
    for token in [
        FAMILY_NO_DECLARATION_ENVELOPE,
        FAMILY_UNFAITHFUL_IMPORT_CONTEXT,
    ] {
        if let Err(reason) = check_family_token(token, FamilyDirection::NoAnswer) {
            panic!("the scorer writes `{token}`, but the guard refuses it: {reason}");
        }
        // A context-construction failure is not a D23 finding.
        assert_family_token_refused(
            token,
            FamilyDirection::Restrictive,
            "is not a `rejected:` token",
        );
    }
}

/// The producer's field mapping, checked with an all-distinct population.
///
/// **The defect this exists for.** Until this test the receipt was assembled by
/// a 25-field struct literal inside the driver, and the driver needs a corpus
/// that is not on this host. So the mapping was written once and executed never.
/// `agree: total.compared` or `oracle_skipped: total.subject_no_answer` would
/// have compiled, kept every conservation law that still happened to balance,
/// and produced a row that reads perfectly. Nothing in the suite could tell.
///
/// **Why every number differs.** A transposition is only detectable if the two
/// fields it swaps hold different values, so the population below uses a
/// distinct value for every count -- and asserts that they ARE distinct, so the
/// premise cannot rot when someone edits a number. The single exception is
/// `unsoundly_permissive`, which is pinned at zero because a nonzero value makes
/// the row mean something else entirely (it changes the class token), and that
/// case is covered by its own mutant in the guard test.
///
/// **What this does not do.** It does not run the lane, score a declaration, or
/// establish that `total` is populated correctly by the scorer -- only that
/// whatever the scorer produces reaches the right cell of the row.
#[test]
fn the_receipt_producer_maps_every_count_to_its_own_field() {
    let mut counts = CorpusCounts {
        decoded: 700_044,
        compared: 600_014,
        agree: 600_000,
        unsoundly_permissive: 0,
        restrictive_with_carve_out: 3,
        restrictive_without_carve_out: 11,
        unscorable: 100_030,
        oracle_skipped: 60_013,
        subject_no_answer: 40_017,
        ..CorpusCounts::default()
    };
    counts
        .restrictive_families
        .insert("rejected:BlockMismatch".to_string(), 4);
    counts
        .restrictive_families
        .insert("rejected:TypeMismatch".to_string(), 10);
    counts.no_answer_families.insert(
        "context:import_context_not_faithfully_representable".to_string(),
        40_000,
    );
    counts
        .no_answer_families
        .insert("inconclusive:Steps".to_string(), 17);

    // The sentinel population must be a LEGAL one, or this test would be
    // asserting the shape of a run that could never occur.
    counts.assert_conservation("sentinel population");

    let spec = CorpusReceiptSpec {
        bead: "franken_lean-t6r7",
        corpus_commit: suite_lock_corpus_commit(),
        seed_modules: 8_009,
        receipt_path_var: "FLN_WHOLE_MATHLIB_RECEIPT",
    };
    let receipt = WholeMathlibReceipt::from_run(&WholeMathlibRunFacts {
        spec: &spec,
        counts: &counts,
        closure_modules: 10_007,
        corpus_fixture_hash: "sentinel-fixture-hash",
        observed_unix_s: 1_786_111_222,
        wall_ms: 12_345_678,
    });

    // THE PREMISE, asserted rather than assumed: distinct values are what make a
    // swap visible, so a later edit that collides two of them must fail here and
    // not silently weaken every assertion below.
    let distinct = [
        ("closure_modules", receipt.closure_modules),
        ("seed_modules", receipt.seed_modules),
        ("decoded", receipt.decoded),
        ("compared", receipt.compared),
        ("agree", receipt.agree),
        (
            "restrictive_with_carve_out",
            receipt.restrictive_with_carve_out,
        ),
        (
            "restrictive_without_carve_out",
            receipt.restrictive_without_carve_out,
        ),
        ("unscorable", receipt.unscorable),
        ("oracle_skipped", receipt.oracle_skipped),
        ("subject_no_answer", receipt.subject_no_answer),
        ("observed_unix_s", receipt.observed_unix_s),
        ("wall_ms", receipt.wall_ms),
    ];
    let mut seen = BTreeMap::new();
    for (field, value) in distinct {
        if let Some(other) = seen.insert(value, field) {
            panic!(
                "the sentinel population gives `{other}` and `{field}` the same value {value}; a \
                 transposition between them would be invisible to every assertion in this test"
            );
        }
    }

    assert_eq!(receipt.bead, "franken_lean-t6r7");
    assert_eq!(receipt.pin, suite_lock_reference_pin());
    assert_eq!(receipt.corpus_commit, suite_lock_corpus_commit());
    assert_eq!(receipt.observed_unix_s, 1_786_111_222);
    assert_eq!(receipt.corpus_fixture_hash, "sentinel-fixture-hash");
    assert_eq!(receipt.closure_modules, 10_007);
    assert_eq!(receipt.seed_modules, 8_009);
    assert_eq!(receipt.decoded, 700_044);
    assert_eq!(receipt.compared, 600_014);
    assert_eq!(receipt.agree, 600_000);
    assert_eq!(receipt.unsoundly_permissive, 0);
    assert_eq!(receipt.restrictive_with_carve_out, 3);
    assert_eq!(receipt.restrictive_without_carve_out, 11);
    assert_eq!(receipt.unscorable, 100_030);
    assert_eq!(receipt.oracle_skipped, 60_013);
    assert_eq!(receipt.subject_no_answer, 40_017);
    assert_eq!(receipt.wall_ms, 12_345_678);

    // THE ONE COUNT THIS SENTINEL LEAVES AT ZERO IS THE ONE THAT MATTERS MOST.
    // Measured over the population above: `unsoundly_permissive` is the ONLY
    // field valued zero. So a producer that ignored the count and wrote a
    // literal zero satisfies every assertion in this test -- and the field is
    // absent from the transposition registry above for the same reason, since
    // there is nothing else at zero for it to collide with. Under D23 an
    // unsoundly permissive row is release-blocking, which makes a field that
    // silently reads zero the worst one to leave unpinned.
    //
    // A second population carries it non-zero. It conserves under all three sum
    // laws -- 21 = 12 + 9, 12 = 5 + 4 + 1 + 2, 9 = 6 + 3 -- and its counts are
    // pairwise distinct, so a transposition INTO this field is visible as well
    // as a hard-coded constant.
    let mut permissive = CorpusCounts {
        decoded: 21,
        compared: 12,
        agree: 5,
        unsoundly_permissive: 4,
        restrictive_with_carve_out: 1,
        restrictive_without_carve_out: 2,
        unscorable: 9,
        oracle_skipped: 6,
        subject_no_answer: 3,
        ..CorpusCounts::default()
    };
    permissive
        .restrictive_families
        .insert("rejected:BlockMismatch".to_string(), 3);
    permissive
        .no_answer_families
        .insert("inconclusive:Steps".to_string(), 3);
    permissive.assert_conservation("permissive sentinel");

    let permissive_receipt = WholeMathlibReceipt::from_run(&WholeMathlibRunFacts {
        spec: &spec,
        counts: &permissive,
        closure_modules: 30,
        corpus_fixture_hash: "permissive-fixture-hash",
        observed_unix_s: 1_700_000_000,
        wall_ms: 77,
    });
    assert_eq!(
        permissive_receipt.unsoundly_permissive, 4,
        "the permissive count must reach its own field. A producer writing a literal zero here \
         passes the sentinel above, where this is the only count that IS zero"
    );
    for (field, value) in [
        ("closure_modules", permissive_receipt.closure_modules),
        ("decoded", permissive_receipt.decoded),
        ("compared", permissive_receipt.compared),
        ("agree", permissive_receipt.agree),
        (
            "restrictive_with_carve_out",
            permissive_receipt.restrictive_with_carve_out,
        ),
        (
            "restrictive_without_carve_out",
            permissive_receipt.restrictive_without_carve_out,
        ),
        ("unscorable", permissive_receipt.unscorable),
        ("oracle_skipped", permissive_receipt.oracle_skipped),
        ("subject_no_answer", permissive_receipt.subject_no_answer),
        ("wall_ms", permissive_receipt.wall_ms),
    ] {
        assert_ne!(
            value, permissive_receipt.unsoundly_permissive,
            "`{field}` shares its value with `unsoundly_permissive`, so a transposition between \
             them would be invisible here too"
        );
    }

    // The census travels in canonical (ascending) order, so two runs that saw
    // the same families produce byte-identical rows.
    assert_eq!(
        receipt.restrictive_families,
        vec![
            "rejected:BlockMismatch=4".to_string(),
            "rejected:TypeMismatch=10".to_string()
        ]
    );
    assert_eq!(
        receipt.no_answer_families,
        vec![
            "context:import_context_not_faithfully_representable=40000".to_string(),
            "inconclusive:Steps=17".to_string()
        ]
    );

    // THE PRODUCER SORTS; THE GUARD DID NOT REQUIRE IT. The assertions above pin
    // the order a receipt is BUILT in. Nothing pinned the order a retained row
    // may be READ in: confirmed by reading the validator and its census helper,
    // which between them hold no ordering check at all, so this reordered row
    // validated before this commit.
    let mut reordered = WholeMathlibReceipt::from_run(&WholeMathlibRunFacts {
        spec: &spec,
        counts: &counts,
        closure_modules: 10_007,
        corpus_fixture_hash: "sentinel-fixture-hash",
        observed_unix_s: 1_786_111_222,
        wall_ms: 12_345_678,
    });
    assert!(
        reordered.restrictive_families.len() >= 2,
        "the census must hold at least two families, or reversing it is a no-op and this cell \
         asserts nothing: {:?}",
        reordered.restrictive_families
    );
    reordered.restrictive_families.reverse();
    assert_ne!(
        reordered.restrictive_families, receipt.restrictive_families,
        "the reversal must actually change the row, or the guard is being asked about the \
         canonical order it already accepts"
    );
    let reordered_reason = reordered
        .validate(&suite_lock_reference_pin(), &suite_lock_corpus_commit())
        .expect_err("a census out of canonical order must not be retained");
    assert!(
        reordered_reason.contains("ascending"),
        "the refusal must be about the order, not about a count or a token: {reordered_reason}"
    );

    // The class is DERIVED from the counts, not chosen: 11 restrictive rows with
    // no carve-out is a refutation and the row must say so.
    assert_eq!(
        receipt.class, "refuted_this_run_found_a_restrictive_divergence",
        "a run that found restrictive divergences must not file the clean class"
    );

    // Provenance the producer reads from the host rather than from the run.
    assert!(!receipt.lane_source_digest_at_run.is_empty());
    assert!(!receipt.target.is_empty());
    assert!(receipt.profile == "dev" || receipt.profile == "release");

    // And the whole thing must satisfy the guard and survive a round trip: a
    // producer that emits rows its own reader refuses is worse than one that
    // emits nothing.
    if let Err(reason) = receipt.validate(&suite_lock_reference_pin(), &suite_lock_corpus_commit())
    {
        panic!("the producer emitted a row its own guard refuses: {reason}");
    }
    let row = receipt.to_row();
    let parsed =
        WholeMathlibReceipt::from_row(&row).expect("a produced row must be readable by the reader");
    assert!(
        parsed == receipt,
        "a produced row must survive its own round trip"
    );
}

/// A receipt describing a clean whole-Mathlib run, used as the GREEN CONTROL for
/// the mutants below. Every mutant is this row with exactly one cell changed, so
/// a mutant that dies names the cell that killed it.
///
/// It is hand-built rather than read from a committed file because no committed
/// file can exist yet: the corpus is host state and is not provisioned here. A
/// fixture is not the production path, and this test says only that the FORMAT
/// refuses what it must — not that any real run was ever scored.
fn sample_whole_mathlib_receipt() -> WholeMathlibReceipt {
    WholeMathlibReceipt {
        bead: "franken_lean-t6r7".to_string(),
        pin: suite_lock_reference_pin(),
        corpus_commit: suite_lock_corpus_commit(),
        observed_unix_s: 1_786_000_000,
        corpus_fixture_hash: "0123456789abcdef".to_string(),
        closure_modules: WHOLE_MATHLIB_MODULE_FLOOR,
        seed_modules: WHOLE_MATHLIB_SEED_FLOOR,
        decoded: WHOLE_MATHLIB_DECODED_FLOOR,
        compared: 600_000,
        agree: 600_000,
        unsoundly_permissive: 0,
        restrictive_with_carve_out: 0,
        restrictive_without_carve_out: 0,
        unscorable: WHOLE_MATHLIB_DECODED_FLOOR - 600_000,
        oracle_skipped: 60_000,
        subject_no_answer: 40_000,
        restrictive_families: Vec::new(),
        no_answer_families: vec![
            "context:import_context_not_faithfully_representable=39000".to_string(),
            "inconclusive:Steps=1000".to_string(),
        ],
        wall_ms: 11_000_000,
        profile: "dev".to_string(),
        target: "x86_64-linux".to_string(),
        lane_source_digest_at_run: "fedcba9876543210".to_string(),
        available_parallelism: 16,
        class: "observed_once_not_an_invariant".to_string(),
    }
}

/// Cut a row at roughly half its length, on a character boundary.
///
/// **`&row[..row.len() / 2]` is a latent panic.** Rust slices strings by BYTE
/// index and refuses an index that falls inside a character, so the midpoint of
/// a row containing any multi-byte content may abort with "byte index is not a
/// char boundary" instead of producing the truncated row the cell wants. It is
/// safe today only because the sample receipt happens to be pure ASCII -- a
/// property of the fixture's current contents, not of the format, and one
/// nothing asserts.
///
/// A row legitimately carries whatever a corpus path, a bead name or a family
/// token contains, and the hostile-field test already proves those are escaped
/// rather than rejected. So the truncation walks back to the nearest boundary
/// rather than trusting the halfway point to be one.
fn truncate_near_half(row: &str) -> String {
    let mut cut = row.len() / 2;
    while cut > 0 && !row.is_char_boundary(cut) {
        cut -= 1;
    }
    row[..cut].to_string()
}

/// Cut a row off immediately after `needle`, so the key is present and only its
/// value's terminator is missing.
///
/// The offset is the needle's own length rather than a literal: a hand-counted
/// `+ 9` is correct exactly until someone edits the needle, and then it is
/// silently pointing into the middle of a value instead of just past it.
fn truncate_after(row: &str, needle: &str) -> String {
    let start = row
        .find(needle)
        .unwrap_or_else(|| panic!("the sample row must contain `{needle}`"));
    row[..start + needle.len()].to_string()
}

/// The census taxonomy is CLOSED, and the `context:` convention was prose.
///
/// **What the prefixes are for.** `check_family_token`'s own documentation says
/// the two context families carry a `context:` prefix "so a reader can tell a
/// kernel outcome token from a context-construction reason". That is the whole
/// interpretability of the TRIAGE line the driver publishes: a family beginning
/// `rejected:` is a D23 finding, `inconclusive:` is an exhaustion,
/// `internal_fault` is a bug, and `context:` is a module our side could not
/// build an environment for. Nothing enforced it. Rename either constant to
/// something unprefixed and every test still passes -- the grammar rule only
/// requires a non-answer NOT to start with `rejected:` -- while the census gains
/// a family a reader cannot place.
///
/// **Closed, not merely prefixed.** The stronger property is that these four
/// shapes are ALL of them. A new emitter adding a fifth would put an
/// unclassifiable family into a published census, and the triage line would
/// still look complete. So the population is assembled from every source a run
/// can draw on -- the kernel's rejection classes from its own source, the
/// resource causes through the production formatter, the two context constants,
/// and the internal-fault token -- and each is required to land in one of the
/// four.
///
/// **All four must actually occur.** A taxonomy check over a population missing
/// a shape proves less than it appears to, so the shapes seen are counted.
#[test]
fn every_family_token_a_run_can_emit_belongs_to_the_closed_taxonomy() {
    // The constants' VALUES, as literals: one side is what the scorer writes,
    // the other is the name the census is read under.
    assert_eq!(
        FAMILY_NO_DECLARATION_ENVELOPE,
        "context:subject_has_no_declaration_envelope"
    );
    assert_eq!(
        FAMILY_UNFAITHFUL_IMPORT_CONTEXT,
        "context:import_context_not_faithfully_representable"
    );

    let mut tokens = vec![
        FAMILY_NO_DECLARATION_ENVELOPE.to_string(),
        FAMILY_UNFAITHFUL_IMPORT_CONTEXT.to_string(),
        "internal_fault".to_string(),
    ];
    for class in reject_class_variants_from_source() {
        tokens.push(format!("rejected:{class}"));
    }
    // EVERY REASON A RUN CAN EMIT, AND TWO WERE MISSING. This list held
    // `ExecutionSteps`, `Cancelled` and `Memory`; `Heartbeats` and
    // `RecursionDepth` were absent, so a test whose name is "every family token a
    // run can emit" was checking four of the six arms of `resource_usage_facts`.
    // `inconclusive:Heartbeats` was produced NOWHERE in this file -- not as a
    // literal, not through this loop -- so nothing had ever seen it.
    //
    // The list is total by the compiler, not by care: `named` matches every
    // variant with no catch-all, so a new `ResourceReason` cannot be added
    // without landing here, and the count below fails if it is added to the
    // taxonomy but not to this population.
    fn named(reason: &ResourceReason) -> &'static str {
        match reason {
            ResourceReason::Heartbeats { .. } => "Heartbeats",
            ResourceReason::ExecutionSteps => "ExecutionSteps",
            ResourceReason::RecursionDepth { .. } => "RecursionDepth",
            ResourceReason::Cancelled => "Cancelled",
            ResourceReason::Memory { .. } => "Memory",
            ResourceReason::StructuralBudget { .. } => "StructuralBudget",
        }
    }
    let reasons = [
        ResourceReason::Heartbeats {
            consumed: 2,
            limit: 1,
        },
        ResourceReason::ExecutionSteps,
        ResourceReason::RecursionDepth { limit: 1 },
        ResourceReason::Cancelled,
        ResourceReason::Memory { limit_bytes: 8 },
        // `StructuralBudget` is carried by the `StructuralUnit::ALL` loop below,
        // which covers its three units rather than one representative.
        ResourceReason::StructuralBudget {
            unit: StructuralUnit::InputBytes,
        },
    ];
    assert_eq!(
        reasons.iter().map(named).collect::<BTreeSet<_>>().len(),
        6,
        "a `ResourceReason` arm is missing from the population this taxonomy is checked over"
    );
    for reason in reasons {
        tokens.push(
            resource_usage_facts(&ResourceUsage {
                reason,
                allowed: 1,
                observed: 2,
            })
            .0,
        );
    }
    for unit in StructuralUnit::ALL {
        tokens.push(
            resource_usage_facts(&ResourceUsage {
                reason: ResourceReason::StructuralBudget { unit },
                allowed: 1,
                observed: 2,
            })
            .0,
        );
    }

    let mut shapes = BTreeSet::new();
    for token in &tokens {
        let shape = if token.starts_with("rejected:") {
            "a D23 finding"
        } else if token.starts_with("inconclusive:") {
            "an exhaustion"
        } else if token.starts_with("context:") {
            "an environment our side could not build"
        } else if token == "internal_fault" {
            "a bug in us"
        } else {
            panic!(
                "`{token}` belongs to none of the four family shapes, so a census carrying it \
                 would publish a row a reader cannot place. Either give it a prefix that says \
                 what kind of thing it is, or widen this taxonomy deliberately"
            )
        };
        shapes.insert(shape);
    }

    assert_eq!(
        shapes.len(),
        4,
        "the population must exercise all four shapes; a taxonomy checked against three of them \
         says nothing about the fourth. Saw: {shapes:?}"
    );
}

/// The floors carry the receipt's whole anti-vacuity argument, and their VALUES
/// rested on nothing.
///
/// **Every use reads the constant.** The driver asserts against them before it
/// compares anything, the receipt guard refuses rows beneath them, the green
/// control sits exactly on them, and the below-floor probes are derived from
/// them. Lower one and all of that moves together: the lane accepts a smaller
/// corpus, the receipt accepts the row describing it, and every test in this
/// file still passes. The values appear exactly three times in the file -- their
/// own definitions.
///
/// **This is not the green-control boundary test.** That one pins where the
/// control sits RELATIVE to the floors and that one unit below is refused, which
/// holds for any values whatsoever. This pins the values themselves, and the
/// relationships that make them coherent.
///
/// **What anchors them.** The bead records a measured preflight over the
/// provisioned corpus (comments 2135/2136, 2026-08-11): 8,264 Mathlib oleans,
/// and a resurrection sweep decoding 567,030 declarations from those seeds. The
/// seed floor sits just below the first, so a truncated checkout fails while the
/// real one passes. The closure floor is higher because the closure adds every
/// `Init`, `Std`, `Lean` and package module Mathlib imports, and the decoded
/// floor higher still because those modules carry declarations, not just names.
/// Those are OBSERVATIONS FROM ANOTHER PANE's run, cited rather than re-measured
/// -- this host has no corpus -- which is exactly why the numbers deserve to be
/// written down where a change has to argue with them.
#[test]
fn the_whole_mathlib_floors_are_anchored_and_coherent() {
    assert_eq!(
        (
            WHOLE_MATHLIB_SEED_FLOOR,
            WHOLE_MATHLIB_MODULE_FLOOR,
            WHOLE_MATHLIB_DECODED_FLOOR
        ),
        (8_000, 10_000, 700_000),
        "these floors are what stop a small tree qualifying as a whole-Mathlib observation. \
         Changing one is a claim about the corpus, not a tuning knob: say which measurement \
         supports the new value"
    );

    // THE RELATIONSHIPS OUTLIVE THE VALUES. Whatever the numbers become, a
    // closure strictly contains its seed set plus everything those seeds import,
    // and modules carry many declarations each. A floor set where declarations
    // were fewer than modules would be describing something that is not a
    // corpus.
    assert!(
        WHOLE_MATHLIB_SEED_FLOOR < WHOLE_MATHLIB_MODULE_FLOOR,
        "the closure contains the seeds and their imports, so its floor cannot be the lower one"
    );
    assert!(
        WHOLE_MATHLIB_DECODED_FLOOR > WHOLE_MATHLIB_MODULE_FLOOR,
        "each module carries many declarations; a decoded floor at or below the module floor \
         would admit a corpus averaging one declaration per module"
    );

    // AND NO FIXTURE IN THIS FILE CAN EVER SATISFY THEM. That is the property
    // the floors exist for, stated directly rather than left implicit in three
    // magnitudes: the largest fixture here holds a handful of files, so the
    // margin is what keeps a receipt built from one refusable.
    assert!(
        WHOLE_MATHLIB_SEED_FLOOR > 100,
        "the floors must sit far above any fixture, or a receipt built from a handful of empty \
         files could pass the guard that exists to refuse exactly that"
    );
}

/// The floors are MINIMUMS, and nothing sat at the edge of one.
///
/// **Every receipt refused for being too small is far too small.** The fixture
/// flow carries three modules and the measured-nothing row carries zero, while
/// the planted control sits orders of magnitude above. Measured against the real
/// comparison and both off-by-one neighbours: `0` and `3` are refused by `<`, by
/// `<=` and by `< FLOOR - 1` alike, so no existing input can tell which one the
/// guard uses.
///
/// **A floor is a minimum, not a threshold to exceed.** A corpus of exactly ten
/// thousand closure modules IS the documented population, and `<=` would refuse
/// it -- a lane that measured precisely what the floor asks for would be told it
/// had measured too little. One module fewer must be refused, which `< FLOOR -
/// 1` would allow. Both boundary values are needed: one pins each side of the
/// comparison, and neither alone says where the edge is.
///
/// **The at-floor receipt has to pass every OTHER rule too**, which is what makes
/// it a real boundary case rather than a shape: it conserves under all three sum
/// laws, its seed set fits inside its closure, its census is empty because it
/// found nothing, and its provenance comes from the producer.
#[test]
fn the_floors_are_minimums_not_thresholds_to_exceed() {
    let pin = suite_lock_reference_pin();
    let corpus = suite_lock_corpus_commit();

    // A receipt sitting on chosen values for the three floors, legal in every
    // other respect. `compared` is derived so the population always conserves.
    let receipt_with = |closure: u64, seed: u64, decoded: u64| {
        let compared = decoded - 100_000;
        let counts = CorpusCounts {
            decoded,
            compared,
            agree: compared,
            unscorable: 100_000,
            oracle_skipped: 100_000,
            ..CorpusCounts::default()
        };
        counts.assert_conservation("floor boundary");
        let spec = CorpusReceiptSpec {
            bead: "franken_lean-t6r7",
            corpus_commit: suite_lock_corpus_commit(),
            seed_modules: seed,
            receipt_path_var: "FLN_WHOLE_MATHLIB_RECEIPT",
        };
        WholeMathlibReceipt::from_run(&WholeMathlibRunFacts {
            spec: &spec,
            counts: &counts,
            closure_modules: closure,
            corpus_fixture_hash: "boundary-fixture-hash",
            observed_unix_s: 1_786_000_000,
            wall_ms: 5,
        })
    };

    // EXACTLY ON EVERY FLOOR MUST PASS.
    if let Err(reason) = receipt_with(
        WHOLE_MATHLIB_MODULE_FLOOR,
        WHOLE_MATHLIB_SEED_FLOOR,
        WHOLE_MATHLIB_DECODED_FLOOR,
    )
    .validate(&pin, &corpus)
    {
        panic!(
            "a receipt sitting exactly on all three floors was refused. A floor is the smallest \
             population that qualifies, so the value AT it qualifies: {reason}"
        );
    }

    // AND ONE BELOW ANY OF THEM MUST NOT, each named by its own floor.
    for (label, receipt, expected) in [
        (
            "closure",
            receipt_with(
                WHOLE_MATHLIB_MODULE_FLOOR - 1,
                WHOLE_MATHLIB_SEED_FLOOR,
                WHOLE_MATHLIB_DECODED_FLOOR,
            ),
            "closure module(s)",
        ),
        (
            "seed",
            receipt_with(
                WHOLE_MATHLIB_MODULE_FLOOR,
                WHOLE_MATHLIB_SEED_FLOOR - 1,
                WHOLE_MATHLIB_DECODED_FLOOR,
            ),
            "seeded Mathlib module(s)",
        ),
        (
            "decoded",
            receipt_with(
                WHOLE_MATHLIB_MODULE_FLOOR,
                WHOLE_MATHLIB_SEED_FLOOR,
                WHOLE_MATHLIB_DECODED_FLOOR - 1,
            ),
            "decoded declaration(s)",
        ),
    ] {
        let reason = match receipt.validate(&pin, &corpus) {
            Err(reason) => reason,
            Ok(()) => panic!("one below the {label} floor must be refused, and was not"),
        };
        assert!(
            reason.contains(expected),
            "the {label} boundary must be refused by ITS OWN floor, not by a neighbouring rule: \
             {reason}"
        );
    }
}

/// Truncating a row never splits a character.
///
/// **The hazard is concrete, not theoretical.** `"aé a"` is five bytes and its
/// midpoint, byte two, lands inside the `é` -- so `&row[..row.len() / 2]` on a
/// row shaped like that aborts rather than truncating. I checked that case
/// before claiming it: several plausible multi-byte strings DO have a boundary
/// at their midpoint, so "contains non-ASCII" is not sufficient to trigger it
/// and the failure would arrive only for some contents.
///
/// The round-trip cell that truncates is meant to test the reader's response to
/// a cut row. If the cut itself panicked, the cell would fail with an arithmetic
/// complaint about indices and say nothing about the reader at all.
#[test]
fn truncating_a_row_never_splits_a_character() {
    // THE FOUR-BYTE ROW EARNS ITS PLACE. Every other case here needs at most ONE
    // byte of walk-back -- measured -- so a cut written as `if !boundary { cut -=
    // 1 }` instead of a loop satisfies all of them. `aa🎯bb` has its midpoint two
    // bytes inside a four-byte character, so a single step leaves the cut still
    // inside it and the slice that follows panics.
    const ROWS: [&str; 7] = [
        "aé a",
        "café au lait",
        "{\"schema\":\"x\",\"bead\":\"franken–lean\"}",
        "",
        "x",
        "ありがとう",
        "aa🎯bb",
    ];
    for row in ROWS {
        let cut = truncate_near_half(row);
        assert!(
            row.starts_with(&cut),
            "the truncation must be a prefix of the row: {cut:?} of {row:?}"
        );
        assert!(
            cut.len() <= row.len() / 2,
            "the truncation must not grow the row: {cut:?} of {row:?}"
        );
        // THE REAL PROPERTY, and my first attempt at it was vacuous: I wrote a
        // UTF-8 round trip, which a `String` passes by construction because it
        // is already valid UTF-8. What matters is where the cut LANDS -- the
        // slice would have panicked before ever producing a String to check.
        assert!(
            row.is_char_boundary(cut.len()),
            "the cut fell inside a character of {row:?} at byte {}",
            cut.len()
        );
    }

    // ANTI-VACUITY: at least one case must actually need the walk-back, or this
    // test is a list of strings whose midpoints were already boundaries. Read
    // from ROWS rather than from a second list of its own: the old version named
    // two strings by hand and would have gone on passing if the loop above had
    // stopped using them.
    assert!(
        ROWS.iter().any(|row| !row.is_char_boundary(row.len() / 2)),
        "no case here has a midpoint inside a character, so nothing exercises the walk-back"
    );

    // AND ONE MUST NEED MORE THAN A SINGLE BYTE OF IT. Without this the list can
    // drift back to characters of two and three bytes whose midpoints always
    // land one step from a boundary, and a cut that steps back once instead of
    // walking would pass again. Computed with `is_char_boundary`, not with the
    // function under test: the midpoint is inside a character AND so is the byte
    // before it.
    assert!(
        ROWS.iter().any(|row| {
            let midpoint = row.len() / 2;
            !row.is_char_boundary(midpoint) && !row.is_char_boundary(midpoint - 1)
        }),
        "every case needs at most one byte of walk-back, so a single step back would satisfy them \
         all and nothing here distinguishes a walk from a step"
    );
}

/// The schema NAME is the retained contract, and its value was pinned nowhere.
///
/// **Producer and reader both read the constant, so the value is unconstrained.**
/// `to_row` writes `WHOLE_MATHLIB_RECEIPT_SCHEMA` and `from_row` compares
/// against it. Change the constant and both move together: every test in this
/// file still passes, and every receipt already retained under the old name
/// becomes unreadable. The round-trip cell that mutates `receipt/1` into
/// `receipt/2` tests that the CHECK works; it says nothing about which name the
/// check is for.
///
/// **The failure is loud but wrong, which is its own hazard.** Unlike the
/// retention directory -- where a change makes the guard report nothing retained
/// -- a changed schema makes it REFUSE every retained row, with a message
/// blaming the row rather than the rename. Whoever sees it is looking at
/// evidence that was valid when it was written and is now being called
/// malformed.
///
/// **So the name is written out here as a literal.** One side is the constant
/// the code uses, the other is the name the retained rows were filed under.
/// Changing the format is then a deliberate act: advance the version suffix,
/// and decide what happens to rows carrying the old one -- rather than a rename
/// that passes CI and quietly invalidates an archive.
#[test]
fn the_receipt_schema_name_is_part_of_the_retained_contract() {
    assert_eq!(
        WHOLE_MATHLIB_RECEIPT_SCHEMA, "fln.whole-mathlib-differential-receipt/1",
        "retained receipts were filed under this exact name. If the format genuinely changed, \
         advance the version suffix and say what becomes of rows carrying the old one; if it did \
         not, this rename would make a valid archive unreadable"
    );
    assert!(
        WHOLE_MATHLIB_RECEIPT_SCHEMA.ends_with("/1"),
        "the trailing version is what a format change advances; without it there is nothing to \
         distinguish an old row from a malformed one"
    );

    // AND A REAL ROW CARRIES IT, FIRST. Checking the constant alone would leave
    // a producer that wrote some other name -- or wrote the schema somewhere in
    // the middle -- entirely unexamined. A reader scanning a mixed NDJSON file
    // identifies a row by the schema it leads with.
    let row = sample_whole_mathlib_receipt().to_row();
    assert!(
        row.starts_with("{\"schema\":\"fln.whole-mathlib-differential-receipt/1\","),
        "a produced row must lead with its schema: {row}"
    );
}

/// The format is strict: a row must re-serialize to the bytes it was read from,
/// and a reader that cannot reproduce a row must refuse it rather than repair it.
#[test]
fn the_whole_mathlib_receipt_round_trips_through_its_own_serializer() {
    let sample = sample_whole_mathlib_receipt();
    let row = sample.to_row();
    let parsed = WholeMathlibReceipt::from_row(&row).expect("the sample row must parse");
    assert_eq!(parsed.to_row(), row, "canonical round trip");
    assert!(
        parsed == sample,
        "the parsed row must equal what produced it"
    );

    // A CHARACTER AFTER A STRING'S CLOSING QUOTE. `text` stops at the first
    // quote after the field opens. With escapes refused, the way left to stop
    // early is a bare quote inside a value -- measured before this commit,
    // `"bead":"a"b"` was read as `a` and accepted. Appending a character after
    // the sample's own bead is the same shape as the exponent two cells down:
    // the value THIS reader returns is unchanged, so every rule that looks at
    // the bead passes exactly as before, and only the character it stopped at
    // differs.
    let trailing = row.replace(
        &format!("\"bead\":\"{}\"", sample.bead),
        &format!("\"bead\":\"{}\"x", sample.bead),
    );
    assert_ne!(
        trailing, row,
        "the surgery must have changed the row, or the sample's bead is not written where it was \
         looked for"
    );
    let trailing_reason = match WholeMathlibReceipt::from_row(&trailing) {
        Err(reason) => reason,
        Ok(read) => panic!(
            "a row whose bead is followed by a stray character was read as {:?}, which is what it \
             reads from the well-formed row -- nothing about the value distinguishes them",
            read.bead
        ),
    };
    assert!(
        trailing_reason.contains("bead") && trailing_reason.contains("punctuation"),
        "the refusal must name the field and say the string did not end where the row's \
         punctuation does: {trailing_reason}"
    );

    // AN EXPONENT APPENDED TO A NUMBER. `number` reads digits and stops at the
    // first character that is not one. Appending `e9` therefore leaves THIS
    // reader's answer identical -- the same value, so every count, floor and sum
    // rule passes exactly as before -- while the file now states a number a
    // billion times larger to anything that parses JSON. Measured before this
    // commit, alongside `700044.5` read as `700044` and `700044abc` read as
    // `700044` from a malformed row.
    assert!(
        sample.wall_ms > 0,
        "the sample's wall_ms must be non-zero, or the truncated read would be refused for being \
         zero and this cell would prove nothing about the terminator"
    );
    let exponent = row.replace(
        &format!("\"wall_ms\":{}", sample.wall_ms),
        &format!("\"wall_ms\":{}e9", sample.wall_ms),
    );
    assert_ne!(
        exponent, row,
        "the surgery must have changed the row, or the sample's wall_ms is not written where it \
         was looked for"
    );
    let exponent_reason = match WholeMathlibReceipt::from_row(&exponent) {
        Err(reason) => reason,
        Ok(read) => panic!(
            "a row stating {}e9 milliseconds was read as {}; this reader's answer is unchanged by \
             the exponent, which is exactly why no other rule can notice it",
            sample.wall_ms, read.wall_ms
        ),
    };
    assert!(
        exponent_reason.contains("wall_ms") && exponent_reason.contains("punctuation"),
        "the refusal must name the field and say the number did not end where the row's \
         punctuation does: {exponent_reason}"
    );

    // A COMMA INSIDE ONE ELEMENT. The extractor splits the array on commas
    // before it looks at quotes, so one element containing a comma is read as
    // two. Measured before this commit: a census listing ONE family named
    // `inconclusive:Steps=1,inconclusive:Depth=2` was read as two families with
    // the same total a genuine two-element array gives -- byte-for-byte the same
    // result, so no count, sum or token rule could tell them apart. Last wave a
    // bracket HID families the row listed; this invents families it does not.
    let invented = row.replace(
        "\"no_answer_families\":[]",
        "\"no_answer_families\":[\"inconclusive:Steps=1,inconclusive:Depth=2\"]",
    );
    assert!(
        invented.contains("[\"inconclusive:Steps=1,inconclusive:Depth=2\"]"),
        "the forged census must be ONE quoted element carrying a comma, or it is an ordinary \
         two-element array and invents nothing: {invented}"
    );
    let invented_reason = match WholeMathlibReceipt::from_row(&invented) {
        Err(reason) => reason,
        Ok(read) => panic!(
            "a row listing 1 no-answer family was read as {}; the reader split an element on its \
             own comma",
            read.no_answer_families.len()
        ),
    };
    assert!(
        invented_reason.contains("no_answer_families")
            && invented_reason.contains("whole quoted element"),
        "the refusal must name the array and say the element is not whole: {invented_reason}"
    );

    // AN ARRAY ELEMENT CARRYING THE ARRAY'S TERMINATOR. `strings` stops at the
    // first `]`, and JSON allows that character inside an element. Measured
    // before this commit: a census listing two families, with the bracket inside
    // the first, was read as ONE family carrying the whole total -- so the triage
    // sums still balanced, every conservation rule still passed, and the second
    // family was simply gone from the row. Totals are what the guard compares;
    // membership is what it loses.
    assert!(
        row.contains("\"no_answer_families\":[]"),
        "the sample's census must be empty for this surgery to build a two-element array: {row}"
    );
    let hidden = row.replace(
        "\"no_answer_families\":[]",
        "\"no_answer_families\":[\"inconclusive:Steps=1]hidden\",\"inconclusive:Depth=2\"]",
    );
    assert!(
        hidden.contains("inconclusive:Steps") && hidden.contains("inconclusive:Depth"),
        "the forged row must LIST both families, or nothing is being hidden: {hidden}"
    );
    let hidden_reason = match WholeMathlibReceipt::from_row(&hidden) {
        Err(reason) => reason,
        Ok(read) => panic!(
            "a row listing 2 no-answer families was read as {}; the reader stopped at a bracket \
             inside an element and dropped the rest",
            read.no_answer_families.len()
        ),
    };
    assert!(
        hidden_reason.contains("no_answer_families") && hidden_reason.contains("dropped"),
        "the refusal must name the array and say entries were lost, not blame a count: \
         {hidden_reason}"
    );

    // A STRING FIELD CARRYING AN ESCAPE. The serializer writes a quote as a
    // backslash-quote pair, and this reader stops at the first plain quote it
    // meets -- which for an escaped value is the escape's own. Measured with
    // exact copies of both functions before this commit: a bead of `a"b` came
    // back as `a` plus a trailing backslash, every other field still parsed, and
    // the row VALIDATED, because a corrupted bead is still non-blank. The bead
    // is what routes a retained observation to whoever owns it.
    let quoted = WholeMathlibReceipt {
        bead: "a\"b".to_string(),
        ..sample_whole_mathlib_receipt()
    };
    let quoted_row = quoted.to_row();
    assert!(
        quoted_row.contains("\\\""),
        "the serializer must escape the quote, or the reader never meets one: {quoted_row}"
    );
    let quoted_reason = match WholeMathlibReceipt::from_row(&quoted_row) {
        Err(reason) => reason,
        Ok(read) => panic!(
            "a bead of {:?} was read back as {:?}; the reader stopped at the escaped quote",
            quoted.bead, read.bead
        ),
    };
    assert!(
        quoted_reason.contains("bead") && quoted_reason.contains("escape"),
        "the refusal must name the field and say the reader cannot decode it: {quoted_reason}"
    );

    // A FIELD NAMED TWICE. This reader finds the FIRST match and a JSON reader
    // takes the last, so before this commit the row below passed every floor
    // here -- 700_000 decoded declarations -- while `jq` over the same file
    // reported 1. Measured, both readings, on one row. The duplicate is refused
    // rather than resolved: whichever value was meant, a row that says both is
    // not evidence.
    let doubled = row.replace("\"decoded\":", "\"decoded\":1,\"filler\":0,\"decoded\":");
    assert_eq!(
        doubled.matches("\"decoded\":").count(),
        2,
        "the planted row must really name the field twice: {doubled}"
    );
    // Matched rather than `expect_err`, which would need the receipt to be
    // `Debug`; what matters if this ever parses is which value it took.
    let doubled_reason = match WholeMathlibReceipt::from_row(&doubled) {
        Err(reason) => reason,
        Ok(read) => panic!(
            "a row naming `decoded` twice was read anyway, as {}; a JSON reader would have taken \
             the other value",
            read.decoded
        ),
    };
    assert!(
        doubled_reason.contains("decoded") && doubled_reason.contains("more than once"),
        "the refusal must name the duplicated field and say what is wrong with it: \
         {doubled_reason}"
    );

    // EACH CELL NAMES THE REFUSAL IT EXPECTS. Until now every one of these
    // asserted only `is_err()`, and `from_row` has SEVEN distinct refusal kinds
    // -- so a reader that rejected everything at the schema check would have
    // satisfied all twelve while five of those kinds did nothing at all. Same
    // defect the receipt mutants had two waves ago, in the other half of this
    // test.
    let mutations: Vec<(&str, String, &str)> = vec![
        (
            "schema moved",
            row.replace("receipt/1", "receipt/2"),
            "receipt schema is",
        ),
        // DELIBERATELY NON-SPECIFIC, and said so rather than dressed up: the cut
        // lands wherever half the row happens to be, so which field goes missing
        // is not a property worth pinning. It asserts only that SOMETHING was
        // missing, which is all a random truncation can honestly claim.
        ("truncated", truncate_near_half(&row), "missing"),
        (
            "field dropped",
            row.replace(",\"wall_ms\":11000000", ""),
            "missing numeric field `wall_ms`",
        ),
        (
            "seed count dropped",
            row.replace(",\"seed_modules\":8000", ""),
            "missing numeric field `seed_modules`",
        ),
        (
            // The needle still matches, so the field is FOUND; the value simply
            // no longer starts with a digit and parses to nothing.
            "whitespace introduced",
            row.replace("\"decoded\":", "\"decoded\": "),
            "field `decoded` is not a u64",
        ),
        // THESE THREE SHARE ONE CAUSE ON PURPOSE. Each parses cleanly and is
        // caught only by re-serialization, so they are told apart by their INPUT
        // rather than their message -- the one place on this bead where a shared
        // fragment is correct rather than a collapsed cell.
        (
            "count reworded but not re-serialized",
            row.replace("\"compared\":600000", "\"compared\":0600000"),
            "not in canonical form",
        ),
        // A KEY CARRIED TWICE. The extractors take the FIRST occurrence, so a
        // second copy appended later is invisible to the reader while being the
        // one a human scanning the file is most likely to read -- the two would
        // then disagree about what the row says, silently. Re-serialization is
        // what closes it: the canonical form has one of each key, so a row with
        // a duplicate cannot be reproduced and is refused rather than
        // half-read.
        (
            "a field carried twice",
            row.replace("\"class\":", "\"compared\":0,\"class\":"),
            "not in canonical form",
        ),
        // The same argument for a key the format does not define at all: the
        // row must be CLOSED, or arbitrary content could ride along in a
        // retained receipt and survive review by not being displayed.
        (
            "an unknown field smuggled in",
            row.replace("\"class\":", "\"reviewed\":\"yes\",\"class\":"),
            "not in canonical form",
        ),
        // THE READER HAS THREE EXTRACTOR KINDS AND ONLY ONE WAS PROBED. `text`,
        // `number` and `array` each refuse a missing key, and `text` and `array`
        // each refuse an unterminated one -- five branches, of which the
        // mutations above reached only `number`'s. Checking some members of a
        // group and not the others is how a gap survives review: the ones that
        // are checked make the group look covered. The truncation case does hit
        // one of these, but it cannot say WHICH, so it would pass even if a
        // single extractor kind were the only one still checking.
        (
            "a string field dropped",
            row.replace(",\"profile\":\"dev\"", ""),
            "missing string field `profile`",
        ),
        (
            "an array field dropped",
            row.replace(",\"restrictive_families\":[]", ""),
            "missing array field `restrictive_families`",
        ),
        // Truncated immediately after a value's opening delimiter, so the key IS
        // found and only its terminator is missing -- the branch a dropped field
        // can never reach.
        (
            "an unterminated string value",
            truncate_after(&row, "\"class\":\""),
            "unterminated string field `class`",
        ),
        (
            "an unterminated array value",
            truncate_after(&row, "\"restrictive_families\":["),
            "unterminated array field `restrictive_families`",
        ),
    ];
    let mut refusals: Vec<(&str, String)> = Vec::new();
    for (name, damaged, expected) in mutations {
        let reason = match WholeMathlibReceipt::from_row(&damaged) {
            Ok(_) => panic!(
                "a receipt with `{name}` was accepted; the reader must refuse what it cannot \
                 reproduce byte for byte"
            ),
            Err(reason) => reason,
        };
        assert!(
            !expected.is_empty(),
            "`{name}` carries an empty expectation, which `contains` satisfies for every \
             message; the cell would pass whatever the reader did"
        );
        assert!(
            reason.contains(expected),
            "`{name}` was refused, but for the wrong reason: expected a message naming \
             `{expected}`, got `{reason}`"
        );
        refusals.push((name, reason));
    }

    // THE FOUR EXTRACTOR CELLS MUST PRODUCE FOUR DIFFERENT REFUSALS. Two name a
    // missing key and two an unterminated value; two of them concern the same
    // field. If any pair collapsed to one message, that pair would no longer be
    // distinguishing the branch each is named for -- and two of these four are
    // the only probe their branch has.
    let extractor_cells = [
        "a string field dropped",
        "an array field dropped",
        "an unterminated string value",
        "an unterminated array value",
    ];
    let distinct = refusals
        .iter()
        .filter(|(name, _)| extractor_cells.contains(name))
        .map(|(_, reason)| reason.as_str())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        distinct.len(),
        extractor_cells.len(),
        "the extractor cells did not produce distinct refusals: {distinct:?}"
    );
}

/// The guard's content rules, run over forged rows.
///
/// The failure this is built against is the empty-referent row: zero
/// divergences over zero comparisons satisfies every naive "was it clean?"
/// check and would stand as the retained evidence for a whole-corpus
/// observation. Each mutant below changes ONE cell of the green control, so a
/// mutant that dies names the cell responsible; the control itself must pass, or
/// every mutant below would die for the wrong reason.
#[test]
fn a_whole_mathlib_receipt_that_measured_nothing_is_refused() {
    let pin = suite_lock_reference_pin();
    let corpus = suite_lock_corpus_commit();
    let sample = sample_whole_mathlib_receipt();
    if let Err(reason) = sample.validate(&pin, &corpus) {
        panic!("the green control must satisfy its own guard, but: {reason}")
    }

    // THE CONTROL SITS EXACTLY ON THREE FLOORS, AND THAT IS THE TEST.
    //
    // Each floor is written `value < FLOOR`, so a row AT the floor must be
    // accepted. Nothing else in this file pins that boundary: every mutant is
    // far below its floor and would still be refused by a `<=`, and every other
    // validating receipt sits comfortably above. The only thing distinguishing
    // `<` from `<=` is that this control's three counts are the floors
    // themselves -- so the green assertion above is doing double duty, and it
    // does it silently.
    //
    // Pinned here because it is a property of the FIXTURE, not of the guard, and
    // fixtures get tidied. Someone raising these to rounder or more "realistic"
    // numbers would remove the only off-by-one check on three floors without
    // touching an assertion or seeing a red.
    assert_eq!(
        (sample.closure_modules, sample.seed_modules, sample.decoded),
        (
            WHOLE_MATHLIB_MODULE_FLOOR,
            WHOLE_MATHLIB_SEED_FLOOR,
            WHOLE_MATHLIB_DECODED_FLOOR
        ),
        "the green control must sit exactly ON each floor: that is what proves the comparison \
         admits a row at the boundary rather than only above it"
    );
    // And one below each is refused -- the other half of the boundary, which the
    // control alone cannot show.
    for (name, break_the_floor) in [
        (
            "one closure module below the floor",
            (|receipt: &mut WholeMathlibReceipt| receipt.closure_modules -= 1)
                as fn(&mut WholeMathlibReceipt),
        ),
        ("one seed module below the floor", |receipt| {
            receipt.seed_modules -= 1
        }),
        ("one decoded declaration below the floor", |receipt| {
            receipt.decoded -= 1;
            // keep the population conserved so the floor is what fires
            receipt.unscorable -= 1;
        }),
    ] {
        let mut probe = sample_whole_mathlib_receipt();
        break_the_floor(&mut probe);
        assert!(
            probe.validate(&pin, &corpus).is_err(),
            "`{name}` was accepted; the floor admits a row beneath it"
        );
    }

    let mutants: Vec<(&str, WholeMathlibReceipt, &str)> = vec![
        (
            "compared nothing",
            WholeMathlibReceipt {
                compared: 0,
                agree: 0,
                unscorable: WHOLE_MATHLIB_DECODED_FLOOR,
                ..sample_whole_mathlib_receipt()
            },
            "zero declarations compared",
        ),
        // THREE FLOORS SHARE THE PHRASE "below the" -- closure, seed and decoded.
        // Two of these cells asserted on that bare fragment, so ANY ONE of the
        // three floors could have been deleted and both cells would still have
        // passed through a sibling's message. Each now asserts on the noun that
        // names its own population.
        (
            "empty closure",
            WholeMathlibReceipt {
                closure_modules: 0,
                ..sample_whole_mathlib_receipt()
            },
            "closure module(s)",
        ),
        (
            "a big closure around a truncated Mathlib",
            WholeMathlibReceipt {
                seed_modules: 12,
                ..sample_whole_mathlib_receipt()
            },
            "still not whole Mathlib",
        ),
        (
            "more seeds than closure",
            WholeMathlibReceipt {
                seed_modules: WHOLE_MATHLIB_MODULE_FLOOR + 1,
                ..sample_whole_mathlib_receipt()
            },
            "cannot exceed the closure",
        ),
        (
            "decoded below the floor",
            WholeMathlibReceipt {
                decoded: 1,
                ..sample_whole_mathlib_receipt()
            },
            // `decoded declaration(s)` alone also appears in
            // `CorpusMatrixReceipt::validate`, a different validator these
            // mutants never reach; the comma keeps the expectation unique
            // file-wide rather than merely unique among the rules under test.
            "decoded declaration(s), below the",
        ),
        (
            "another Reference epoch",
            WholeMathlibReceipt {
                pin: "v0.0.0".to_string(),
                ..sample_whole_mathlib_receipt()
            },
            "epoch",
        ),
        (
            "another corpus revision",
            WholeMathlibReceipt {
                corpus_commit: "0".repeat(40),
                ..sample_whole_mathlib_receipt()
            },
            "another corpus",
        ),
        (
            "no observation instant",
            WholeMathlibReceipt {
                observed_unix_s: 0,
                ..sample_whole_mathlib_receipt()
            },
            "observed_unix_s",
        ),
        (
            "no elapsed time",
            WholeMathlibReceipt {
                wall_ms: 0,
                ..sample_whole_mathlib_receipt()
            },
            // NOT the bare `wall_ms`: the profile refusal explains that
            // `wall_ms` is uninterpretable without knowing the profile, so it
            // contains that word too. `wall_ms: 0` is what belongs to this rule
            // alone.
            "wall_ms: 0",
        ),
        // OVERFLOW IS A REFUSAL, NOT A PANIC. Each of these makes one sum in
        // `validate` exceed u64, and each must name ITS OWN sum -- the messages
        // differ only in the label, so a cell asserting on `overflows a u64`
        // alone would pass for either.
        (
            "the population sum overflows",
            WholeMathlibReceipt {
                compared: u64::MAX,
                unscorable: 1,
                ..sample_whole_mathlib_receipt()
            },
            "`compared + unscorable` overflows",
        ),
        (
            "the direction buckets overflow",
            WholeMathlibReceipt {
                agree: u64::MAX,
                unsoundly_permissive: 1,
                ..sample_whole_mathlib_receipt()
            },
            "`the D23 direction buckets` overflows",
        ),
        (
            "population does not conserve",
            WholeMathlibReceipt {
                unscorable: 0,
                ..sample_whole_mathlib_receipt()
            },
            "conserve its own population",
        ),
        (
            "direction buckets do not conserve",
            WholeMathlibReceipt {
                agree: 1,
                ..sample_whole_mathlib_receipt()
            },
            "D23 direction buckets",
        ),
        (
            "restrictive rows left untriaged",
            WholeMathlibReceipt {
                agree: 599_990,
                restrictive_without_carve_out: 10,
                class: "refuted_this_run_found_a_restrictive_divergence".to_string(),
                ..sample_whole_mathlib_receipt()
            },
            "partial triage",
        ),
        (
            "unscorable population does not split",
            WholeMathlibReceipt {
                oracle_skipped: 59_999,
                ..sample_whole_mathlib_receipt()
            },
            "split its unscorable population",
        ),
        (
            "non-answers left untriaged",
            WholeMathlibReceipt {
                no_answer_families: Vec::new(),
                ..sample_whole_mathlib_receipt()
            },
            "no_answer_families triages",
        ),
        (
            "a restrictive row triaged to a non-rejection",
            WholeMathlibReceipt {
                agree: 599_990,
                restrictive_without_carve_out: 10,
                restrictive_families: vec!["inconclusive:Steps=10".to_string()],
                class: "refuted_this_run_found_a_restrictive_divergence".to_string(),
                ..sample_whole_mathlib_receipt()
            },
            "is not a `rejected:` token",
        ),
        (
            "a non-answer triaged to a rejection",
            WholeMathlibReceipt {
                no_answer_families: vec!["rejected:BlockMismatch=40000".to_string()],
                ..sample_whole_mathlib_receipt()
            },
            "is a `rejected:` token",
        ),
        // BOTH DELIMITERS, not just the one that came to mind. The rule loops
        // over `[',', '=']` and only the comma had a cell. The two fail
        // differently and the comma cell cannot stand in for the equals one: a
        // comma splits an entry into two, while an `=` makes the split AMBIGUOUS
        // -- `context:a=b=40000` can be read as family `context:a` with the
        // nonsense count `b=40000`, or as family `context:a=b` with count 40000,
        // and `rsplit_once` silently picks the second. Two readers of the same
        // retained row would disagree about which family was counted. The
        // expectations name the offending character so neither cell can pass in
        // the other's place.
        (
            "a family name carrying the entry separator",
            WholeMathlibReceipt {
                no_answer_families: vec!["context:a,b=40000".to_string()],
                ..sample_whole_mathlib_receipt()
            },
            "`,` this format",
        ),
        (
            "a family name carrying the count separator",
            WholeMathlibReceipt {
                no_answer_families: vec!["context:a=b=40000".to_string()],
                ..sample_whole_mathlib_receipt()
            },
            "`=` this format",
        ),
        (
            "a family counted twice",
            WholeMathlibReceipt {
                no_answer_families: vec![
                    "inconclusive:Steps=20000".to_string(),
                    "inconclusive:Steps=20000".to_string(),
                ],
                ..sample_whole_mathlib_receipt()
            },
            "twice",
        ),
        // NEITHER OF THE NEXT TWO CAN BE PRODUCED BY A RUN, and that is the
        // point rather than a reason to skip them. Family tokens come from
        // `UnitOutcome::outcome`, which is never empty, or from the two
        // `context:` constants; and an ACCEPTED outcome routes to neither
        // census, so `accepted` can never enter one. The retained file is
        // append-only and editable by hand, so the guard's job is to refuse rows
        // no producer would have written -- those are precisely the rows nothing
        // upstream can be relied on to prevent.
        (
            "a family entry with no family name",
            WholeMathlibReceipt {
                restrictive_families: vec!["=5".to_string()],
                ..sample_whole_mathlib_receipt()
            },
            "names no family",
        ),
        (
            "an agreement counted as a non-answer",
            WholeMathlibReceipt {
                no_answer_families: vec!["accepted=40000".to_string()],
                ..sample_whole_mathlib_receipt()
            },
            "is the ACCEPTED token",
        ),
        (
            "a family count that is not a number",
            WholeMathlibReceipt {
                restrictive_families: vec!["rejected:BlockMismatch=two".to_string()],
                ..sample_whole_mathlib_receipt()
            },
            "non-u64 count",
        ),
        (
            "a family that triages nobody",
            WholeMathlibReceipt {
                no_answer_families: vec![
                    "context:import_context_not_faithfully_representable=40000".to_string(),
                    "inconclusive:Steps=0".to_string(),
                ],
                ..sample_whole_mathlib_receipt()
            },
            "counts zero rows",
        ),
        (
            "a family entry that is not family=count",
            WholeMathlibReceipt {
                no_answer_families: vec!["inconclusive:Steps".to_string()],
                ..sample_whole_mathlib_receipt()
            },
            "is not `family=count`",
        ),
        (
            "no corpus provenance",
            WholeMathlibReceipt {
                corpus_fixture_hash: String::new(),
                ..sample_whole_mathlib_receipt()
            },
            "corpus_fixture_hash",
        ),
        (
            "no bead attribution",
            WholeMathlibReceipt {
                bead: "   ".to_string(),
                ..sample_whole_mathlib_receipt()
            },
            "names no work item",
        ),
        (
            "a profile the producer cannot emit",
            WholeMathlibReceipt {
                profile: "fastbuild".to_string(),
                ..sample_whole_mathlib_receipt()
            },
            "only `dev` or `release`",
        ),
        (
            "no host architecture",
            WholeMathlibReceipt {
                target: String::new(),
                ..sample_whole_mathlib_receipt()
            },
            "names no host architecture",
        ),
        (
            "no source provenance",
            WholeMathlibReceipt {
                lane_source_digest_at_run: String::new(),
                ..sample_whole_mathlib_receipt()
            },
            "lane_source_digest_at_run",
        ),
        (
            "a restrictive divergence wearing the clean class",
            WholeMathlibReceipt {
                agree: 599_990,
                restrictive_without_carve_out: 10,
                restrictive_families: vec!["rejected:BlockMismatch=10".to_string()],
                ..sample_whole_mathlib_receipt()
            },
            "counts earn refuted_this_run_found_a_restrictive_divergence",
        ),
        (
            "an unsound acceptance wearing the clean class",
            WholeMathlibReceipt {
                agree: 599_999,
                unsoundly_permissive: 1,
                ..sample_whole_mathlib_receipt()
            },
            "counts earn refuted_this_run_accepted_what_the_reference_rejected",
        ),
    ];

    let mut observed: Vec<(&str, String, &str)> = Vec::new();
    for (name, mutant, expected) in mutants {
        let verdict = mutant.validate(&pin, &corpus);
        let reason = match verdict {
            Ok(()) => panic!(
                "the receipt guard ACCEPTED a row that `{name}`. Every rule here exists \
                 because a row of that shape would otherwise stand as retained evidence"
            ),
            Err(reason) => reason,
        };
        // The cross-product check below would also fail on an empty expectation
        // -- it matches every other cell's refusal -- but it would report a
        // collision rather than the real fault, so the vacuity is named here.
        assert!(
            !expected.is_empty(),
            "`{name}` carries an empty expectation, which matches every message"
        );
        assert!(
            reason.contains(expected),
            "`{name}` was refused for the wrong reason: expected a message naming \
             `{expected}`, got `{reason}`"
        );
        observed.push((name, reason, expected));
    }

    // EVERY EXPECTATION MUST IDENTIFY ITS OWN CELL, checked against the real
    // refusals rather than by reading the messages.
    //
    // Four waves of this bead were spent finding, by hand, cells whose expected
    // fragment was also emitted by a DIFFERENT rule -- three floors sharing
    // "below the", two delimiters sharing "as a delimiter". Each time, either
    // rule could have been deleted and both cells would still have passed. This
    // makes the property standing instead of remembered: if any refusal here
    // contains another cell's expectation, the two are interchangeable and this
    // fails naming both.
    //
    // It compares the strings the guard actually produced. An earlier attempt to
    // derive the same thing by scanning the source for message literals returned
    // a confidently wrong answer -- it truncated `validate` at the first nested
    // brace and matched code fragments -- which is exactly why the comparison
    // belongs here, where no parsing is involved.
    if let Err(collision) = expectations_are_mutually_exclusive(&observed) {
        panic!("{collision}");
    }
}

/// No cell's refusal may contain another cell's expectation.
///
/// **Extracted so it can be shown to fire.** Inline, this ran only over the real
/// mutant list, where every expectation is currently distinct -- so it never
/// reported anything, and a broken version of it (comparing a cell only with
/// itself, say, or skipping on the wrong key) would have gone on reporting
/// nothing. That is the shape this bead keeps finding, and it applies to the
/// guards that protect the other guards just as much as to the product.
fn expectations_are_mutually_exclusive(observed: &[(&str, String, &str)]) -> Result<(), String> {
    for (name, reason, _) in observed {
        for (other_name, _, other_expected) in observed {
            if name == other_name {
                continue;
            }
            if reason.contains(other_expected) {
                return Err(format!(
                    "the refusal for `{name}` contains `{other_expected}`, which is the \
                     expectation belonging to `{other_name}`. The two cells cannot tell each \
                     other's rule apart, so either rule could be deleted and both would still \
                     pass. Assert on the part that differs"
                ));
            }
        }
    }
    Ok(())
}

/// The collision detector detects collisions -- and does not report them where
/// there are none.
///
/// **Both polarities, because either alone is satisfiable by a broken check.** A
/// detector that always returned `Ok` would pass the first case; one that always
/// returned `Err` would pass the second. Only the pair pins the behaviour.
///
/// **The third case is the claim a comment makes elsewhere, made checkable.** The
/// mutant loop guards against an empty expectation separately, on the grounds
/// that this detector would flag it as a COLLISION and so blame the wrong thing.
/// That reasoning is asserted here rather than left as prose: an empty
/// expectation does produce a collision report, which is precisely why the
/// narrower guard upstream is worth having.
#[test]
fn the_expectation_collision_detector_reports_only_real_collisions() {
    let distinct: Vec<(&str, String, &str)> = vec![
        (
            "alpha",
            "row records wall_ms: 0 and nothing else".to_string(),
            "wall_ms: 0",
        ),
        (
            "beta",
            "row carries an empty target".to_string(),
            "empty target",
        ),
    ];
    assert!(
        expectations_are_mutually_exclusive(&distinct).is_ok(),
        "two cells whose expectations appear in neither other's refusal are not a collision"
    );

    // `alpha`'s refusal happens to contain `beta`'s expectation.
    let colliding: Vec<(&str, String, &str)> = vec![
        (
            "alpha",
            "row records wall_ms: 0, and an empty target would also be refused".to_string(),
            "wall_ms: 0",
        ),
        (
            "beta",
            "row carries an empty target".to_string(),
            "empty target",
        ),
    ];
    let report = expectations_are_mutually_exclusive(&colliding)
        .expect_err("a refusal containing another cell's expectation is a collision");
    assert!(
        report.contains("alpha") && report.contains("beta") && report.contains("empty target"),
        "the report must name both cells and the shared fragment, or it says a collision exists \
         without saying between what: {report}"
    );

    // An empty expectation matches every message, so it reads as a collision.
    let vacuous: Vec<(&str, String, &str)> = vec![
        ("alpha", "row records wall_ms: 0".to_string(), "wall_ms: 0"),
        ("beta", "row carries an empty target".to_string(), ""),
    ];
    assert!(
        expectations_are_mutually_exclusive(&vacuous).is_err(),
        "an empty expectation is contained by every refusal, which is why the mutant loop \
         refuses one directly rather than leaving this detector to blame a collision"
    );

    // THE COLLISION IN THE OTHER DIRECTION. Both cases above put the containment
    // the same way round -- the FIRST cell's refusal holding the SECOND cell's
    // expectation -- so a scan over ordered pairs `i < j` reports both of them
    // and cannot be told apart from one over EVERY ordered pair. Measured before
    // this case was added: distinct ok/ok, forward REPORTS/REPORTS, vacuous
    // REPORTS/REPORTS, and this one REPORTS/ok.
    //
    // A collision is symmetric -- two cells that cannot tell each other's rule
    // apart are in that state whichever refusal happens to quote the other -- so
    // a detector that only looked one way would miss half of them, and the half
    // it missed would be silent rather than loud.
    let backward: Vec<(&str, String, &str)> = vec![
        ("alpha", "row records wall_ms: 0".to_string(), "wall_ms: 0"),
        (
            "beta",
            "row carries an empty target, and wall_ms: 0 would also be refused".to_string(),
            "empty target",
        ),
    ];
    // THE DIRECTION IS ASSERTED, NOT ASSUMED. If a later edit made alpha's
    // refusal mention `empty target` as well, a one-directional scan would
    // report this case too and it would quietly become a copy of the first.
    assert!(
        !backward[0].1.contains(backward[1].2),
        "the first cell's refusal must NOT contain the second's expectation, or this is the \
         forward case again"
    );
    assert!(
        backward[1].1.contains(backward[0].2),
        "the second cell's refusal must contain the first's expectation, or there is no collision \
         here at all"
    );
    let backward_report = expectations_are_mutually_exclusive(&backward)
        .expect_err("which cell's refusal quotes the other cannot change whether they collide");
    assert!(
        backward_report.contains("alpha")
            && backward_report.contains("beta")
            && backward_report.contains("wall_ms: 0"),
        "the report must name both cells and the shared fragment, whichever way round the \
         containment runs: {backward_report}"
    );
}

/// Read a retained receipt file: absent, present, or present-and-unreadable.
///
/// **Three outcomes, and the guard collapsed two of them.** It matched any
/// `Err` from `read_to_string` and reported `none_retained` -- so a file that
/// EXISTS but cannot be read, because a write was interrupted and left invalid
/// UTF-8, or because its permissions changed, was announced as "no receipt is
/// retained". That is the green silence this same test was repaired for two
/// waves ago when the DIRECTORY could move: a passing run stating there is
/// nothing to check, about evidence that is sitting right there.
///
/// Absent is the only outcome that earns the quiet arm, and it is the only one
/// nobody can fix from the repository. Anything else is a fault about a file
/// that exists, and the corpus classifier already draws exactly this line for
/// the corpus root -- it was simply never drawn here.
fn read_retained_rows(path: &Path) -> Result<Option<String>, String> {
    match fs::read_to_string(path) {
        Ok(text) => Ok(Some(text)),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(format!(
            "the retained receipt file {} exists but could not be read: {error}. That is not the \
             same as nothing being retained -- an unreadable file is evidence in an unknown \
             state, and reporting it as absent would hide it",
            path.display()
        )),
    }
}

/// Validate EVERY row a retained receipt file holds, and say how many there were.
///
/// **Why this is a function rather than a loop inside the guard.** The file is
/// opened with `append(true)`, so after two runs it holds two rows and after
/// twenty it holds twenty: MULTI-ROW IS THE STEADY STATE, not an edge case. The
/// loop that walks it lived inside a guard which only ever executes against the
/// real file -- absent on every host so far -- and it panicked rather than
/// returning, so nothing could probe it. A guard that silently stopped after the
/// first row would let every subsequent run's observation into the tree
/// unchecked, and the file would look examined because its first line was.
///
/// Returning `Result` is what lets the controls assert a LATER row is caught;
/// an assertion inside cannot be caught.
/// A field named twice makes a row mean two things at once.
///
/// These readers locate a field with `str::find`, which takes the FIRST match.
/// A JSON reader takes the last. So a row carrying `"decoded":700000` and later
/// `"decoded":1` passes every floor here while `jq` over the same file reports a
/// number below all of them -- measured, both readings, on one row. The retained
/// file is editable by hand, which is the only reason that matters.
///
/// Refusing the duplicate removes the disagreement rather than picking a winner:
/// whichever value was meant, a row that says both is not evidence.
fn assert_field_once(row: &str, key: &str, needle: &str) -> Result<(), String> {
    if row.matches(needle).count() > 1 {
        return Err(format!(
            "field `{key}` appears more than once. This reader takes the first value and a JSON \
             reader takes the last, so the row would mean different things to different readers"
        ));
    }
    Ok(())
}

/// This reader returns raw text and does not decode escapes.
///
/// `json_string` writes a quote as a backslash-quote pair. The extractor stops
/// at the first plain quote it finds, which for an escaped value is the escape's
/// own quote -- so a bead of `a"b` is written escaped and read back as `a` plus
/// a trailing backslash. Measured with exact copies of both functions: the value
/// is corrupted, every other field still parses, and the row VALIDATES, because
/// a corrupted bead is still non-blank. The bead is the routing field; a mangled
/// one names no work item.
///
/// Refusing is the honest half of a reader that cannot decode. Nothing the
/// producer legitimately writes carries a backslash -- pins, commits, hex
/// digests, target triples, the class token -- so this refuses exactly the rows
/// it cannot read correctly.
fn assert_no_escape(key: &str, value: &str) -> Result<(), String> {
    if value.contains('\\') {
        return Err(format!(
            "string field `{key}` carries a backslash escape, and this reader returns raw text \
             without decoding escapes; the value it read is not the value that was written"
        ));
    }
    Ok(())
}

/// The bracket this reader stops at must be the array's own.
///
/// `strings` takes the FIRST `]` after the array opens. JSON allows that
/// character inside an element, so one planted there ends the array early and
/// every entry after it disappears. Measured: a census listing two families,
/// with the terminator inside the first, is read as ONE family carrying the
/// whole total -- so the triage sums still balance, every conservation rule
/// still passes, and a divergence family is simply gone from the row.
///
/// In a well-formed row both arrays are followed by `,` (they sit before
/// `wall_ms`), so the character after the real terminator is punctuation. If it
/// is anything else, the bracket belonged to an element and the array was cut
/// short.
fn assert_array_terminator(key: &str, rest: &str, end: usize) -> Result<(), String> {
    match rest[end..].chars().nth(1) {
        Some(',') | Some('}') | None => Ok(()),
        Some(other) => Err(format!(
            "array field `{key}` is followed by `{other}` where the row's punctuation belongs, so \
             the bracket this reader stopped at came from inside an element and every entry after \
             it was dropped"
        )),
    }
}

/// An array element must be a whole quoted string.
///
/// `strings` splits the array on commas BEFORE it looks at quotes, so a comma
/// inside one element is read as two. Measured: a census listing ONE family
/// named `rejected:A=5,rejected:B=3` is read as two families totalling 8 --
/// byte-for-byte the same result this reader gives for a genuine two-element
/// array, so no count, sum or token rule can tell them apart. The census would
/// name families the row does not contain, which is the mirror of a bracket
/// hiding families it does.
fn assert_whole_quoted_element(key: &str, item: &str) -> Result<(), String> {
    if item.len() < 2 || !item.starts_with('"') || !item.ends_with('"') {
        return Err(format!(
            "array field `{key}` holds `{item}`, which is not a whole quoted element. This reader \
             splits on commas before it looks at quotes, so a comma inside one element is read as \
             two families the row never listed"
        ));
    }
    Ok(())
}

/// A number must end where the row's punctuation begins.
///
/// `number` reads digits and stops at the first character that is not one,
/// keeping whatever it has. Measured against what a JSON reader sees: `700044.5`
/// is read as `700044`, `700044abc` is read as `700044` from a malformed row,
/// and `7e5` is read as `7` where JSON says `700000`. The last is the shape that
/// matters -- an exponent appended to a value leaves this reader's answer
/// UNCHANGED while multiplying the file's by a billion, so every count rule
/// passes exactly as before and the row means something else entirely to
/// anything that parses it properly.
fn assert_number_terminator(key: &str, rest: &str, end: usize) -> Result<(), String> {
    match rest[end..].chars().next() {
        Some(',') | Some('}') | None => Ok(()),
        Some(other) => Err(format!(
            "numeric field `{key}` is followed by `{other}` where the row's punctuation belongs. \
             This reader stops at the first non-digit and keeps what it has, so the value it read \
             is not the value the row states"
        )),
    }
}

/// A string must end where the row's punctuation begins.
///
/// The last of the three extractors to get this check. `text` stops at the first
/// quote after the field opens; with escapes now refused, the remaining way to
/// stop early is a bare quote in the middle of a value. Measured: `"bead":"a"b"`
/// is read as `a` and accepted, and the character after the quote this reader
/// stopped at is `b` rather than the row's comma. The bead is the routing field,
/// so the row would name the wrong work item while validating.
///
/// **Whitespace is refused too, deliberately.** ` ,` after a value is legal JSON
/// and this rule rejects it, as the sibling rules already reject it after a
/// number or an array. The producer never writes it, and accepting it would mean
/// this reader has to skip whitespace everywhere else -- which it does not, so
/// accepting it here would be a promise the rest of the reader cannot keep.
fn assert_string_terminator(key: &str, rest: &str, end: usize) -> Result<(), String> {
    match rest[end..].chars().nth(1) {
        Some(',') | Some('}') | None => Ok(()),
        Some(other) => Err(format!(
            "string field `{key}` is followed by `{other}` where the row's punctuation belongs, so \
             the quote this reader stopped at came from inside the value and the text it read is \
             shorter than the row states"
        )),
    }
}

/// How many statements of a claim a line-by-line scan cannot see.
///
/// The document guard below decides per LINE whether a line states the
/// determinism claim, and then whether that line names its scope. A claim broken
/// across a line break is stated by neither half, so it is qualified by nobody
/// and counted by nothing -- the scan silently redefines its own denominator,
/// which is a failure this repository has met before under a different name.
///
/// Measured at this commit: zero sites in either document are hidden this way,
/// so the population is empty and the synthetic member below is what keeps the
/// rule honest. The first measurement I took said two were hidden; it compared
/// LINES CONTAINING the phrase against OCCURRENCES of it, which is the same
/// denominator error one artifact up. The green control for a line stating the
/// claim twice is there because of it.
fn claim_sites_hidden_by_a_line_break(text: &str) -> usize {
    let per_line: usize = text.lines().map(thread_matrix_claim_count).sum();
    thread_matrix_claim_count(text).saturating_sub(per_line)
}

/// Where a stale claim about the matrix straddles a line break.
///
/// The sibling of `claim_sites_hidden_by_a_line_break`, for the other scan in
/// the same loop. That one asks whether ONE phrase is visible; this one asks
/// whether a CONJUNCTION is -- the stale rule fires only when a single line
/// mentions the matrix and calls it missing, so "the corpus-scale matrix" on one
/// line and "does not exist" on the next is caught by neither half.
///
/// Returns the 1-based number of the first line of such a run. Runs where one
/// line alone already states both are excluded: those belong to the per-line
/// rule, and reporting them here would blame the wrong line.
///
/// A PAIR IS NOT THE WIDEST A SENTENCE WRAPS. This scanned two lines at a time,
/// so "the corpus-scale matrix" / "does" / "not exist yet" was stated by no
/// line, by no pair, and therefore by nothing -- the same join the claim scan
/// carried until the previous commit, one rule over. Measured: old `None`, new
/// `Some(1)`.
///
/// The widening stops at a blank line, and that bound is load-bearing rather
/// than decorative: without it `AGENTS.md:1155` is reported, where a sentence
/// naming the matrix is followed by a paragraph break and then, in a different
/// paragraph, a phrase from the stale list. Joining across a paragraph is how a
/// scan of this shape starts inventing sites, so the plant below pins the
/// refusal.
fn stale_claim_split_across_lines(text: &str, stale: &[&str]) -> Option<usize> {
    /// A hard-wrapped sentence spans a few lines, not a section.
    const WIDEST_STRADDLE: usize = 3;
    let lines = text.lines().collect::<Vec<_>>();
    let states_it = |line: &str| {
        let text = stale_scan_form(line);
        text.contains("matrix") && stale.iter().any(|s| text.contains(s))
    };
    (2..=WIDEST_STRADDLE).find_map(|width| {
        lines.windows(width).enumerate().find_map(|(index, run)| {
            if run.iter().any(|line| states_it(line))
                || run.iter().any(|line| line.trim().is_empty())
            {
                return None;
            }
            let joined = stale_scan_form(&run.join(" "));
            let split = joined.contains("matrix") && stale.iter().any(|s| joined.contains(s));
            split.then_some(index + 1)
        })
    })
}

/// Claim sites that name neither their scope nor the corpus lane's cadence.
///
/// The scanned documents must satisfy both rules per site. The derived scope
/// applies the same conjunction, so a document outside the list cannot pass by
/// naming one and omitting the other.
/// Whether a line states the thread-matrix claim, however it spaces it.
///
/// Matching the exact literal misses `{1,8,32}`. That is not hypothetical: the
/// plan's PG-5 gate row spells it without spaces, says "per commit", and names
/// no scope -- so the row that DEFINES the gate is the one site no rule could
/// see. Whitespace is stripped before the comparison so a spelling cannot hide a
/// claim.
///
/// AND NEITHER MAY A SPELLING WITH NO BRACES AT ALL. Requiring the brace form
/// left a document free to write "compared at 1, 8 and 32 threads per commit",
/// naming no scope, and be seen by nothing -- the permissive direction, where a
/// site escapes the rule rather than being wrongly caught by it. The prose form
/// counts only where the segment also says "thread", because the three numbers
/// alone are a list of sections, not a claim about determinism.
///
/// AND THAT NOUN MUST BE NEAR THE NUMERALS, NOT MERELY IN THE SAME SEGMENT. The
/// first version of this rule asked whether the SEGMENT said "thread", and the
/// hidden-site rule hands it a WHOLE DOCUMENT -- so an unrelated "sections 1, 8
/// and 32" anywhere in a file that mentions threads scored as a claim visible
/// only to the whole-text call and to no line, which the hidden-site rule then
/// reports as a wrapped site nobody wrote. A guard that invents a site is worse
/// than one that misses it, because the honest repair for it is to weaken the
/// guard. Measured, planted below: whole-segment 1 hidden site, local 0.
///
/// The window is taken on char boundaries. A byte window panics on the em dash
/// in `AGENTS.md` -- measured, not feared -- and a panicking guard is an
/// invariant failure, not a diagnostic.
fn thread_matrix_claim_sites(segment: &str) -> Vec<usize> {
    /// How far from the numerals the noun may sit and still be about them.
    const NEAR: usize = 40;
    let stripped = whitespace_free(segment).to_ascii_lowercase();
    let mut sites: Vec<usize> = stripped
        .match_indices("{1,8,32}")
        .map(|(at, _)| at)
        .collect();
    for prose in ["1,8and32", "1,8,and32", "1,8or32"] {
        for (at, hit) in stripped.match_indices(prose) {
            let mut low = at.saturating_sub(NEAR);
            while !stripped.is_char_boundary(low) {
                low -= 1;
            }
            let mut high = (at + hit.len() + NEAR).min(stripped.len());
            while !stripped.is_char_boundary(high) {
                high += 1;
            }
            if stripped[low..high].contains("thread") {
                sites.push(at);
            }
        }
    }
    sites
}

/// Every markdown document in the repository, not merely the ones at its root.
///
/// The derived scope read `read_dir` at the TOP LEVEL, so it covered ten files
/// and could not see the other thirteen. A claim in `crates/*/tests/*.md` or
/// `tribunal/fixtures/*/*.md` was outside every rule here -- the scope was
/// derived in the dimension that had already bitten (new root documents) and
/// hand-shaped in the one that had not (depth).
///
/// THE SKIP IS A RULE, NOT A LIST, because a hand-listed scope is what this
/// paragraph exists to stop being. Directories whose name begins with `.` are
/// not repository documents (`.git`, and this host's untracked `.ntm` scratch,
/// which no guard may be allowed to redden). `target` is build output. `vendor`
/// is upstream's text, 61 tracked markdown files of it, and our determinism
/// claim is not stated there -- scanning it would report on Lean's prose as
/// though we had written it. Each exception is refused in the fixture below.
///
/// `file_type` does not follow symlinks, so a symlinked directory is never
/// descended and the walk cannot cycle. The order is sorted: a scope that
/// depends on directory order is not a scope.
fn markdown_documents_below(root: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(directory) = pending.pop() {
        let Ok(entries) = fs::read_dir(&directory) else {
            continue;
        };
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            let Ok(kind) = entry.file_type() else {
                continue;
            };
            // THE DOT RULE IS ABOUT NAMES, NOT ABOUT DIRECTORIES. Applying it to
            // directories alone left `./._COMPREHENSIVE_PLAN...|....md` in scope
            // -- 4096 bytes of untracked editor droppings sitting in the root,
            // which the scan at the previous commit was already reading. It
            // states the claim zero times, so nothing is red today; the hazard is
            // that ANY untracked markdown a pane leaves in the root is scanned,
            // and one containing the claim reddens the guard for every pane over
            // a file that is not part of the repository. Nothing is deleted here:
            // the file is excluded by rule and reported.
            if name.starts_with('.') {
                continue;
            }
            if kind.is_dir() {
                if name == "target" || name == "vendor" {
                    continue;
                }
                pending.push(entry.path());
            } else if kind.is_file() && name.ends_with(".md") {
                found.push(entry.path());
            }
        }
    }
    found.sort();
    found
}

/// A contraction is a spelling, and the stale list is literal.
///
/// The same shape that hid the PG-5 gate row for four commits: a rule written
/// against one wording, and a document free to use another. "the corpus-scale
/// matrix doesn't exist" is the natural way to write the retracted claim and
/// matches none of the four needles; so does the typographic apostrophe that a
/// markdown editor inserts without being asked. Expanded here rather than added
/// to the list, because the list would then need every contraction of every
/// phrase it ever grows.
fn contractions_expanded(text: &str) -> String {
    text.replace('\u{2019}', "'")
        .replace("doesn't", "does not")
        .replace("don't", "do not")
        .replace("isn't", "is not")
        .replace("hasn't", "has not")
        .replace("hadn't", "had not")
        .replace("wasn't", "was not")
}

/// The documents this repository reads line by line rather than by allowance.
///
/// Written out THREE times before this: once in the allowance tier to skip them,
/// once in the strict tier to read them, and once again in a different guard
/// entirely (`the_corpus_matrix_observation_is_retained_and_bound_to_the_current_pin`).
/// Three copies of one decision, and nothing joining them -- so a document added
/// to the strict tier would still be skipped-and-unread if the first copy were
/// missed, and the other guard would go on checking a pair while this one
/// checked a triple. The conservation count below is what makes the join
/// observable: every document in scope is either skipped here or examined here,
/// and the skipped ones are exactly these.
const SCANNED_DOCUMENTS: [&str; 2] = ["AGENTS.md", "README.md"];

/// The one form the stale rules read, and the ORDER is load-bearing.
///
/// Case was the last spelling this rule could not see. Its anchor tested
/// `contains("matrix")`, so a sentence opening "Matrix runs are unbuilt" named a
/// subject the rule did not recognise, and every needle was lowercase too.
///
/// Lowercasing happens BEFORE the contractions are expanded, because the
/// expansion itself matches lowercase: "Doesn't exist" at the start of a
/// sentence survives an expand-then-lowercase pipeline untouched and is caught
/// by neither half. Two normalisations composed in the wrong order leave a gap
/// that neither has alone, which is the same join this guard has now met in
/// four separate rules.
fn stale_scan_form(segment: &str) -> String {
    contractions_expanded(&segment.to_ascii_lowercase())
}

/// The one place a segment is collapsed, so every rule below indexes the same
/// string. Positions from one of them are meaningless against another otherwise,
/// and this guard has already shipped two scans that recognised different claims.
fn whitespace_free(segment: &str) -> String {
    segment.chars().filter(|c| !c.is_whitespace()).collect()
}

fn thread_matrix_claim_count(segment: &str) -> usize {
    thread_matrix_claim_sites(segment).len()
}

/// Whether a qualifying word sits near the claim rather than merely on its line.
///
/// A CLAIM LINE HERE IS A PARAGRAPH. `AGENTS.md:316` is 3359 characters with
/// whitespace removed, so "does this line mention the corpus" asks almost
/// nothing: a word 3000 characters away, in a different sentence, about a
/// different subject, satisfied the rule. R4 wants the scope stated WHERE THE
/// CLAIM IS MADE, and a line is not a place.
///
/// Measured at every real site before choosing the bound -- the qualifier is
/// within 70 collapsed characters at all five qualified sites, the cadence
/// within 318, on lines up to 3359. 600 clears the widest real distance by
/// nearly twice and still refuses a different sentence of the same paragraph.
/// Case is preserved: lowercasing here would widen which words count, and this
/// cell is not the place to do that.
fn qualifier_is_near_the_claim(line: &str, words: &[&str], within: usize) -> bool {
    let dense = whitespace_free(line);
    let sites = thread_matrix_claim_sites(line);
    words.iter().any(|word| {
        let needle = whitespace_free(word);
        dense
            .match_indices(&needle)
            .any(|(at, _)| sites.iter().any(|&site| site.abs_diff(at) <= within))
    })
}

fn states_thread_matrix_claim(line: &str) -> bool {
    thread_matrix_claim_count(line) > 0
}

/// A qualifier belongs to the sentence stating the claim, not to the paragraph.
///
/// Named once, at module scope, because the two tiers of this guard read it. The
/// allowance tier (documents this test does not otherwise check) and the strict
/// tier (`AGENTS.md`, `README.md`) had already drifted apart twice: first on
/// which spelling counts as the claim, then on how near the qualifier must sit.
/// A bound that lives inside one of them is a bound the other cannot honour.
const NEARBY_QUALIFIER: usize = 600;

fn unscoped_claim_sites(text: &str, qualifiers: &[&str], cadence: &[&str]) -> usize {
    const NEARBY: usize = NEARBY_QUALIFIER;
    text.lines()
        .filter(|line| states_thread_matrix_claim(line))
        .filter(|line| {
            !qualifier_is_near_the_claim(line, qualifiers, NEARBY)
                || !qualifier_is_near_the_claim(line, cadence, NEARBY)
        })
        .count()
}

fn validate_retained_receipts(text: &str, pin: &str, corpus_commit: &str) -> Result<usize, String> {
    let rows = text
        .lines()
        .filter(|row| !row.trim().is_empty())
        .collect::<Vec<_>>();
    // Present but empty is a DIFFERENT thing from absent, and it is a failure: a
    // file somebody created and then emptied is not a lighter claim than one that
    // was never written, it is a retracted observation left in place.
    if rows.is_empty() {
        return Err(
            "holds no rows. An empty receipt file is not a lighter claim than an absent one; it \
             is an observation that was removed without being retracted"
                .to_string(),
        );
    }
    for (index, row) in rows.iter().enumerate() {
        let receipt = WholeMathlibReceipt::from_row(row)
            .map_err(|reason| format!("row {index}: {reason}"))?;
        receipt
            .validate(pin, corpus_commit)
            .map_err(|reason| format!("row {index} is retained but not valid: {reason}"))?;
    }
    Ok(rows.len())
}

/// ONE RECEIPT IS ONE LINE, whatever a field contains.
///
/// **What depends on it.** The retained file is line-oriented:
/// `validate_retained_receipts` splits on `\n` and treats each piece as a row.
/// If any field could carry a raw newline, one receipt would arrive as two
/// fragments -- and the guard would then be reading rows that no producer wrote,
/// with the split falling wherever the hostile content put it. A second, forged
/// "row" could be smuggled inside a legitimate one, and every count on either
/// side of the break would belong to neither receipt.
///
/// **Nothing asserted this.** `json_string` escapes newlines, returns, tabs and
/// control characters, so the property holds -- but it held by the escaper's good
/// behaviour alone, and the escaper is shared with several other row formats in
/// this file. A change made for one of those would silently break the retention
/// file's framing here.
///
/// **The row is also required to be REFUSED, not merely contained.** Surviving as
/// one line is the framing property; being rejected by the reader is the content
/// property. Both matter, and they are different: a hostile row that stayed on
/// its own line but was ACCEPTED would corrupt nothing structurally and
/// everything semantically.
#[test]
fn a_receipt_row_is_one_line_even_when_a_field_is_hostile() {
    // Every character the escaper special-cases, plus a bare control byte.
    let hostile = "a\nb\r\nc\td\"e\\f\u{1}g";
    let mut receipt = sample_whole_mathlib_receipt();
    receipt.bead = hostile.to_string();
    receipt.corpus_fixture_hash = hostile.to_string();
    receipt.target = hostile.to_string();
    receipt.no_answer_families = vec![format!("context:{hostile}=40000")];

    let row = receipt.to_row();
    assert!(
        !row.contains('\n') && !row.contains('\r'),
        "a receipt row carried a raw line break, so one receipt would arrive as two rows: {row:?}"
    );
    assert_eq!(
        row.lines().count(),
        1,
        "a receipt must occupy exactly one line of the retained file"
    );

    // FRAMING HOLDS UNDER THE REAL SPLITTER: a good row beside a hostile one is
    // two rows, not three, and the hostile one is refused rather than
    // half-read.
    let good = sample_whole_mathlib_receipt().to_row();
    let file = format!("{good}\n{row}\n");
    assert_eq!(
        file.lines().filter(|line| !line.trim().is_empty()).count(),
        2,
        "the hostile receipt split its own row; the file no longer frames one receipt per line"
    );
    let reason = validate_retained_receipts(
        &file,
        &suite_lock_reference_pin(),
        &suite_lock_corpus_commit(),
    )
    .expect_err("a row carrying escaped control characters must not be retained");
    assert!(
        reason.contains("row 1"),
        "the refusal must blame the hostile row, not its innocent neighbour: {reason}"
    );
}

/// Absent, present, and present-but-unreadable are three different answers.
///
/// **Demonstrated, because a preventive guard nobody exercises is one whose own
/// failure modes nobody sees.** All three arms are driven here: a path that is
/// not there, a readable file, and a file holding bytes that are not UTF-8 --
/// which is what an interrupted append leaves behind, and the most plausible way
/// a real retained file becomes unreadable.
///
/// The unreadable case must NOT be reported as absent. That is the whole point
/// of the split, and without this control the difference would be a claim in a
/// comment.
#[test]
fn an_unreadable_retained_file_is_not_reported_as_absent() {
    let base = Path::new(env!("CARGO_TARGET_TMPDIR")).join("t6r7-retained-read-v1");
    fs::create_dir_all(&base).expect("create the retained-read fixture directory");

    // ABSENT.
    let missing = base.join("not-there.jsonl");
    assert!(!missing.exists());
    assert_eq!(
        read_retained_rows(&missing),
        Ok(None),
        "a path that is not there is the one outcome that earns the quiet arm"
    );

    // PRESENT AND READABLE.
    let readable = base.join("readable.jsonl");
    fs::write(&readable, "one row\n").expect("write the readable fixture");
    assert_eq!(
        read_retained_rows(&readable),
        Ok(Some("one row\n".to_string()))
    );

    // PRESENT AND UNREADABLE: a lone continuation byte is not valid UTF-8, which
    // is what a half-finished append leaves.
    let corrupt = base.join("corrupt.jsonl");
    fs::write(&corrupt, [b'{', 0xFF, b'}', b'\n']).expect("write the corrupt fixture");
    let fault = read_retained_rows(&corrupt)
        .expect_err("a file that exists but cannot be decoded is not an absent file");
    assert!(
        fault.contains("exists but could not be read"),
        "the fault must say the file is THERE and unreadable, not that nothing is retained: \
         {fault}"
    );
    assert!(
        fault.contains("corrupt.jsonl"),
        "the fault must name the file so it can be inspected: {fault}"
    );

    // ANTI-VACUITY: the corrupt fixture must really be undecodable, or the case
    // above would be passing on a file that is merely unusual.
    assert!(
        String::from_utf8(fs::read(&corrupt).expect("re-read the corrupt fixture")).is_err(),
        "the corrupt fixture decodes cleanly, so nothing here exercises the unreadable arm"
    );
}

/// A retained file is checked ROW BY ROW, including the rows after the first.
///
/// **The bug this is aimed at.** The receipt file accumulates one row per run.
/// If the guard checked only the first, a corrupt or wrong-epoch row appended by
/// any later run would sit in the tree as retained evidence while the guard went
/// on passing -- and the file would look examined, because its first line was.
/// Every negative control below puts the bad row LAST, so passing requires the
/// walk to reach it.
#[test]
fn a_retained_receipt_file_is_validated_row_by_row() {
    let pin = suite_lock_reference_pin();
    let corpus = suite_lock_corpus_commit();
    let good = sample_whole_mathlib_receipt().to_row();

    // A file that has been appended to several times is the ordinary case.
    assert_eq!(
        validate_retained_receipts(&format!("{good}\n{good}\n{good}\n"), &pin, &corpus),
        Ok(3),
        "three appended observations must all be read"
    );
    // Blank lines are separators, not rows.
    assert_eq!(
        validate_retained_receipts(&format!("{good}\n\n   \n{good}\n"), &pin, &corpus),
        Ok(2)
    );

    // Nothing at all, and nothing but whitespace, are both refusals.
    for empty in ["", "\n", "   \n\t\n"] {
        let reason = validate_retained_receipts(empty, &pin, &corpus)
            .expect_err("an empty retained file must be refused");
        assert!(reason.contains("holds no rows"), "{reason}");
    }

    // A LATER row that is invalid must be caught, and named by its index.
    let wrong_epoch = WholeMathlibReceipt {
        pin: format!("{pin}-not-this-epoch"),
        ..sample_whole_mathlib_receipt()
    }
    .to_row();
    let reason =
        validate_retained_receipts(&format!("{good}\n{good}\n{wrong_epoch}\n"), &pin, &corpus)
            .expect_err("a wrong-epoch row in third position must be refused");
    assert!(
        reason.contains("row 2") && reason.contains("epoch"),
        "the refusal must name WHICH row failed, or a multi-row file cannot be repaired: {reason}"
    );

    // A LATER row that is unreadable must be caught too -- a different failure
    // path (the reader) from the one above (the guard).
    let reason = validate_retained_receipts(
        &format!("{good}\n{{\"schema\":\"fln.whole-mathlib-differential-receipt/1\"}}\n"),
        &pin,
        &corpus,
    )
    .expect_err("an unreadable row in second position must be refused");
    assert!(
        reason.contains("row 1"),
        "the refusal must name the unreadable row: {reason}"
    );

    // ANTI-VACUITY: the good row must really be good, or every case above would
    // fail for the wrong reason.
    assert_eq!(validate_retained_receipts(&good, &pin, &corpus), Ok(1));
}

/// Every whole-Mathlib receipt retained for the CURRENT pin must satisfy the
/// guard its own producer writes to.
///
/// **Why this does not fail when the file is absent, and why that is not a
/// loophole.** The corpus the lane needs is host state. It is not provisioned
/// here today, so no run can have produced a row, so demanding a committed file
/// would be a standing red for a missing input rather than for a defect -- a red
/// that fires for a cause nobody can fix from the repository is one everybody
/// learns to ignore, which is worse than no guard at all.
///
/// **What stops it from being decorative.** A guard over an empty population is
/// vacuously green and would stay green if `validate` were gutted tomorrow. So
/// the population is not the only thing checked: a PLANTED synthetic receipt and
/// a forged counterpart run on EVERY invocation, so the guard's machinery is
/// exercised whether or not a real row exists. If `validate` stopped refusing
/// what it must, this test would go red today, with no corpus and no receipt.
///
/// **What a green run here earns.** Nothing about the corpus, the kernel, or any
/// Mathlib declaration. Only this: no retained row for this pin contradicts
/// itself or the pin it is filed under. When the absent case fires it prints a
/// typed row saying so, because "the guard passed" and "there was nothing to
/// check" must not be the same observation in a log.
#[test]
fn a_retained_whole_mathlib_receipt_is_bound_to_its_pin_and_corpus() {
    let pin = suite_lock_reference_pin();
    let corpus = suite_lock_corpus_commit();

    // THE PLANTED MEMBER, unconditionally. A green control that must pass and a
    // forgery that must not, so an empty population cannot make this vacuous.
    if let Err(reason) = sample_whole_mathlib_receipt().validate(&pin, &corpus) {
        panic!("the planted control receipt must satisfy the guard, but: {reason}");
    }
    let forged = WholeMathlibReceipt {
        pin: format!("{pin}-not-this-epoch"),
        ..sample_whole_mathlib_receipt()
    };
    let forged_reason = forged.validate(&pin, &corpus).expect_err(
        "the guard accepted a receipt filed under another Reference epoch; with no retained \
             rows to check, this planted pair is the ONLY thing keeping this test honest",
    );
    // AND REFUSED FOR THE PIN, not for something incidental about the sample.
    // A bare `is_err()` here would keep passing if the planted row started
    // failing on, say, a floor -- and since this pair is the only live check
    // when no receipt has been retained, that would leave the epoch binding
    // completely unexercised while the test stayed green.
    assert!(
        forged_reason.contains("epoch") && forged_reason.contains("not-this-epoch"),
        "the refusal must name the epoch mismatch and the offending pin: {forged_reason}"
    );

    // THE FORGERY ABOVE CARRIES A PIN. AN EMPTY ONE DOES NOT, AND WAS UNTESTED.
    // Measured against both the real rule and one that reads an empty field as
    // "the producer did not record this, so do not complain": the decorated pin
    // is refused by both, a NEIGHBOURING epoch is refused by both, and only an
    // empty pin separates them.
    //
    // That reading is a plausible thing to write here, because `pin` and
    // `corpus_commit` are the only two identity fields with no emptiness rule of
    // their own -- `corpus_fixture_hash`, `lane_source_digest_at_run`, `bead`
    // and `target` each have one. Someone adding emptiness handling for
    // consistency could easily write it as a skip rather than a refusal, and the
    // equality is the only thing standing in the way.
    //
    // A receipt carrying no epoch would then validate against ANY epoch: evidence
    // filed under nothing, accepted by whichever run asked for it.
    assert!(
        !forged.pin.is_empty(),
        "the forgery above must carry a pin, or it already covers this case and the two cells are \
         the same cell"
    );
    let unpinned = WholeMathlibReceipt {
        pin: String::new(),
        ..sample_whole_mathlib_receipt()
    };
    let unpinned_reason = unpinned
        .validate(&pin, &corpus)
        .expect_err("a receipt recording no epoch at all must not validate against one");
    assert!(
        unpinned_reason.contains("epoch"),
        "an absent pin must be refused as an epoch mismatch, not left to some later field rule: \
         {unpinned_reason}"
    );

    // THE SAME HOLE ON THE OTHER HALF OF THE BINDING. The corpus commit is bound
    // by an equality too, and nothing else requires it to be present.
    let uncommitted = WholeMathlibReceipt {
        corpus_commit: String::new(),
        ..sample_whole_mathlib_receipt()
    };
    let uncommitted_reason = uncommitted
        .validate(&pin, &corpus)
        .expect_err("a receipt recording no corpus commit must not validate against one");
    assert!(
        uncommitted_reason.contains("corpus commit"),
        "an absent corpus commit must be refused as a corpus mismatch: {uncommitted_reason}"
    );

    // BLANK IS NOT EMPTY, AND TWO OF THE FOUR RULES COULD NOT TELL. Every
    // planted emptiness decoy in this file is `String::new()` -- measured, there
    // is not one whitespace-only plant anywhere -- so nothing distinguished
    // `is_empty()` from `trim().is_empty()`. `bead` and `target` already
    // trimmed; `corpus_fixture_hash` and `lane_source_digest_at_run` did not,
    // so a hash of spaces named no corpus revision and validated anyway, which
    // is precisely what its own refusal says it prevents.
    //
    // Both now trim. These two cells are what keeps them there.
    const BLANK: &str = "   ";
    assert!(
        !BLANK.is_empty() && BLANK.trim().is_empty(),
        "the planted value must be blank WITHOUT being empty, or it does not distinguish the two \
         rules and this cell repeats the ones above"
    );

    let blank_hash = WholeMathlibReceipt {
        corpus_fixture_hash: BLANK.to_string(),
        ..sample_whole_mathlib_receipt()
    };
    let blank_hash_reason = blank_hash
        .validate(&pin, &corpus)
        .expect_err("a corpus fixture hash of spaces names no corpus revision");
    assert!(
        blank_hash_reason.contains("corpus_fixture_hash"),
        "the refusal must name the blank field, not some later rule: {blank_hash_reason}"
    );

    let blank_digest = WholeMathlibReceipt {
        lane_source_digest_at_run: BLANK.to_string(),
        ..sample_whole_mathlib_receipt()
    };
    let blank_digest_reason = blank_digest
        .validate(&pin, &corpus)
        .expect_err("a lane source digest of spaces names no producing source");
    assert!(
        blank_digest_reason.contains("lane_source_digest_at_run"),
        "the refusal must name the blank field: {blank_digest_reason}"
    );

    // AND THE TWO THAT ALREADY TRIMMED STILL DO, which is the evidence for
    // "two of the four" rather than a claim about code nobody re-read.
    let blank_bead = WholeMathlibReceipt {
        bead: BLANK.to_string(),
        ..sample_whole_mathlib_receipt()
    };
    assert!(
        blank_bead
            .validate(&pin, &corpus)
            .is_err_and(|reason| reason.contains("bead")),
        "`bead` trimmed before this commit and must go on doing so"
    );

    // THE REAL POPULATION, which may legitimately be empty at this commit.
    let path = whole_mathlib_receipt_path(&pin);
    let text = match read_retained_rows(&path).unwrap_or_else(|fault| panic!("{fault}")) {
        Some(text) => text,
        None => {
            println!(
                "{{\"schema\":\"fln-t6r7-mathlib-receipt-retention/1\",\"status\":\"none_retained\",\
                 \"pin\":{},\"corpus_commit\":{},\"path\":{},\"reason\":{},\
                 \"claims\":\"the guard machinery was exercised against a planted control only; \
                 NO whole-Mathlib run is evidenced by this test passing\"}}",
                json_string(&pin),
                json_string(&corpus),
                json_string(&path.display().to_string()),
                json_string("no such file"),
            );
            return;
        }
    };

    let rows = match validate_retained_receipts(&text, &pin, &corpus) {
        Ok(rows) => rows,
        Err(reason) => panic!("{}: {reason}", path.display()),
    };
    // THE SUCCESS ROW NEEDS ITS LIMITS MORE THAN THE FAILURE ROW DOES. The
    // `none_retained` case above carefully says it evidences nothing; this one
    // said only `validated`, and it is the row somebody would quote. What it
    // establishes is narrow: every retained row for this pin is internally
    // consistent and filed under the right epoch and corpus. A row's
    // self-consistency says NOTHING about the run that produced it -- a
    // hand-written row satisfying every law validates exactly as well as an
    // observed one, which is the whole reason the producer digests its own
    // source into the row rather than trusting the file.
    println!(
        "{{\"schema\":\"fln-t6r7-mathlib-receipt-retention/1\",\"status\":\"validated\",\
         \"pin\":{},\"corpus_commit\":{},\"rows\":{},\
         \"claims\":\"every retained row is self-consistent and bound to this pin and corpus. \
         NOT that the lane ran, that any corpus was walked, or that any Mathlib declaration was \
         checked -- a row's internal consistency is independent of whether it was observed.\"}}",
        json_string(&pin),
        json_string(&corpus),
        rows,
    );
}

/// The receipt path is keyed by the Reference pin, so advancing `SUITE.lock`
/// retires every retained observation by construction rather than by anyone
/// remembering to.
#[test]
fn the_whole_mathlib_receipt_path_is_keyed_by_the_reference_pin() {
    let pin = suite_lock_reference_pin();
    let path = whole_mathlib_receipt_path(&pin);
    assert!(
        path.ends_with(format!("{pin}.jsonl")),
        "the receipt file must be named for the pin it observes: {}",
        path.display()
    );

    // THE DIRECTORY IS HALF THE ADDRESS, AND ONLY THE FILENAME WAS PINNED.
    //
    // The retention guard reads this path; the producer advertises it. Move the
    // directory and nothing fails: the guard finds no file, takes its
    // `none_retained` arm, and reports that NO receipt is retained -- for a
    // corpus run that retained one, which is now sitting unread in the old
    // location. A green run saying "nothing to check" about evidence that
    // exists is worse than a red.
    //
    // The two components are written here as literals rather than taken from
    // the helper, for the same reason the corpus root is: one side is the
    // implementation, the other is the address it is supposed to have.
    let containing = path.parent().expect("the receipt path has a directory");
    assert_eq!(
        containing.file_name().and_then(|name| name.to_str()),
        Some("whole_mathlib_differential"),
        "retained receipts must live in the directory the guard reads and the producer names: {}",
        path.display()
    );
    assert_eq!(
        containing
            .parent()
            .and_then(|evidence| evidence.file_name())
            .and_then(|name| name.to_str()),
        Some("evidence"),
        "the receipt directory must sit under `evidence/`, beside the other retained artifacts: \
         {}",
        path.display()
    );
    assert_ne!(
        whole_mathlib_receipt_path("v0.0.0"),
        path,
        "two Reference epochs must not share a receipt file"
    );

    // AND THAT ASSERTION IS LEXICAL WHERE ITS CLAIM IS NOT. Both pins it
    // compares are ordinary names, so it cannot distinguish "keyed by the pin"
    // from "keyed by whatever the pin's characters do to a path". Measured:
    // `v1/../v2` and `v2` build paths that compare UNEQUAL and resolve to the
    // same file, so the check above would pass while two epochs shared a
    // receipt.
    for ordinary in [pin.as_str(), "v0.0.0"] {
        assert!(
            !ordinary.contains('/') && !ordinary.contains(".."),
            "`{ordinary}` must be an ordinary name, or the pair above already covers this and \
             the cell below distinguishes nothing"
        );
    }
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let escaping = std::panic::catch_unwind(|| whole_mathlib_receipt_path("v1/../v2"));
    std::panic::set_hook(previous);
    let payload = escaping
        .err()
        .unwrap_or_else(|| panic!("a pin that is not a single path component must be refused"));
    let message = payload
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| payload.downcast_ref::<&str>().copied())
        .unwrap_or_default();
    assert!(
        message.contains("v1/../v2") && message.contains("single ordinary path component"),
        "the refusal must name the pin and the rule it breaks: {message}"
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
        mathlib_modules.len() as u64 >= WHOLE_MATHLIB_SEED_FLOOR,
        "whole-Mathlib differential seed floor: {} < {WHOLE_MATHLIB_SEED_FLOOR}",
        mathlib_modules.len()
    );
    let corpus_commit = suite_lock_corpus_commit();
    let seed_modules = mathlib_modules.len() as u64;
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
            module_floor: WHOLE_MATHLIB_MODULE_FLOOR,
            decoded_floor: WHOLE_MATHLIB_DECODED_FLOOR,
            compared_floor: mathlib_oracle_applicable,
            oracle_total_timeout: WHOLE_MATHLIB_ORACLE_TOTAL_TIMEOUT,
            oracle_process_timeout: WHOLE_MATHLIB_ORACLE_PROCESS_TIMEOUT,
            oracle_modules_per_process: WHOLE_MATHLIB_ORACLE_MODULES_PER_PROCESS,
            label: "pinned-whole-mathlib",
            receipt: Some(CorpusReceiptSpec {
                bead: "franken_lean-t6r7",
                corpus_commit,
                seed_modules,
                receipt_path_var: "FLN_WHOLE_MATHLIB_RECEIPT",
            }),
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
            receipt: None,
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
    /// `Some` only for lanes that retain a pin-keyed receipt. The pinned
    /// present-olean lane does not: its corpus IS the Reference library, so
    /// `SUITE.lock`'s corpus commit would name a revision it never read, and a
    /// receipt whose provenance field is about another input is worse than none.
    receipt: Option<CorpusReceiptSpec>,
}

/// What a receipt-retaining lane must name about itself before it may file a row.
struct CorpusReceiptSpec {
    bead: &'static str,
    corpus_commit: String,
    /// How many modules the lane SEEDED, as opposed to how many its import
    /// closure reached. The driver is corpus-generic and only ever sees the
    /// closure, so this number can only come from the lane that chose the seeds.
    seed_modules: u64,
    /// Environment variable naming the file the row is appended to. The row is
    /// ALWAYS printed; it is written into the tree only when an operator names a
    /// path, because a test that edits a tracked file on its own is a
    /// governed-input mutation and could void another lane's run.
    receipt_path_var: &'static str,
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
        receipt: receipt_spec,
    } = scope;
    let started = Instant::now();
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
            let mut counts = CorpusCounts {
                decoded: module.decoded,
                unscorable: module.decoded,
                oracle_skipped,
                subject_no_answer: module.decoded - oracle_skipped,
                ..CorpusCounts::default()
            };
            // The whole module is unscorable because we could not faithfully
            // rebuild its import context. That is the single largest
            // non-answer family in every corpus run to date, so it is named
            // here rather than left as an untriaged remainder.
            if counts.subject_no_answer != 0 {
                counts.no_answer_families.insert(
                    FAMILY_UNFAITHFUL_IMPORT_CONTEXT.to_string(),
                    counts.subject_no_answer,
                );
            }
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
    // THE TRIAGE, PUBLISHED WITH THE COUNTS IT EXPLAINS (bead `franken_lean-t6r7`).
    // Printed for EVERY receipt-retaining and non-retaining lane alike, because
    // the pinned present-olean lane files no receipt and its rejection families
    // would otherwise exist only as thousands of individual `finding:` lines
    // nobody aggregates. An empty census prints as `none`, so a run that
    // triaged nothing is visibly distinct from a run whose census was dropped.
    let render = |census: &BTreeMap<String, u64>| {
        if census.is_empty() {
            "none".to_string()
        } else {
            family_census_rows(census).join(",")
        }
    };
    println!(
        "kernel_reference_corpus TRIAGE: corpus={corpus_label} \
         restrictive_families={} no_answer_families={} \
         means=restrictive_rows_are_D23_findings_no_answer_rows_are_unscorable_and_say_nothing_about_kernel_completeness",
        render(&total.restrictive_families),
        render(&total.no_answer_families),
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
    // THE RETAINED EVIDENCE (bead `franken_lean-t6r7`), emitted BEFORE the
    // terminal assertions on purpose. A run that found a divergence is exactly
    // the run whose row must survive; filing it after the asserts would retain
    // only the clean observations and quietly discard every refutation.
    if let Some(spec) = receipt_spec {
        let receipt = WholeMathlibReceipt::from_run(&WholeMathlibRunFacts {
            spec: &spec,
            counts: &total,
            closure_modules: inventory.modules.len() as u64,
            corpus_fixture_hash: &inventory.fixture_hash,
            observed_unix_s: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .map(|since| since.as_secs())
                .unwrap_or(0),
            wall_ms: u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX),
        });
        let row = receipt.to_row();
        eprintln!("kernel_reference_corpus RECEIPT: {row}");
        eprintln!(
            "kernel_reference_corpus RECEIPT-DESTINATION: pin_keyed_path={}              written_only_when={} is_set",
            whole_mathlib_receipt_path(&suite_lock_reference_pin()).display(),
            spec.receipt_path_var
        );
        if let Ok(path) = std::env::var(spec.receipt_path_var) {
            let mut file = fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(&path)
                .unwrap_or_else(|error| panic!("open receipt {path}: {error}"));
            writeln!(file, "{row}")
                .unwrap_or_else(|error| panic!("append receipt {path}: {error}"));
        }
    }

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

/// Every `ResourceReason` maps to its own token, in the right slot.
///
/// **Only one of six arms was ever pinned.**
/// `assert_structural_budget_resource_facts_are_total` proves the
/// `StructuralBudget` arm total over `StructuralUnit::ALL`, and is deliberately
/// called before the pin-gated skip so it runs on a host with no Reference. The
/// other five arms of `resource_usage_facts` had nothing. `inconclusive:Steps`
/// and `inconclusive:Depth` appear all over this file, but as LITERALS in census
/// fixtures and fault rows -- never as this function's output.
/// `inconclusive:Heartbeats` and `inconclusive:Memory` occur exactly once each in
/// the whole file: at the arm that produces them.
///
/// **The slots are the part that can be wrong while still looking right.** The
/// facts triple is `(token, steps, depth)`. `RecursionDepth` puts `observed` in
/// the DEPTH slot and zero in steps; `Heartbeats`, `ExecutionSteps` and `Memory`
/// do the opposite. Swap those two and an exhaustion at depth 900 is filed as
/// 900 STEPS at depth 0 -- a well-formed evidence row, a plausible number, and
/// the wrong cause. The observed value here is 900 precisely so a swap shows up
/// as 900-versus-0 rather than as zero-versus-zero.
///
/// **Distinct tokens, because a merge is invisible downstream.** Two reasons
/// sharing an outcome token collapse into one census family, and the census
/// would balance perfectly while attributing every heartbeat exhaustion to
/// something else. `ExecutionSteps` exists specifically to NOT borrow the
/// heartbeat name, per its own doc; nothing checked that they still differ.
///
/// **Exhaustiveness is the compiler's, not a hand-list's.** `witness` matches
/// every variant with no catch-all, so adding a `ResourceReason` fails to
/// compile HERE -- which drags whoever adds it to the list three lines below.
/// That coupling is the honest limit: the list itself is written by hand, and
/// what makes it maintainable is that nobody can extend the taxonomy without
/// being sent to this function.
#[test]
fn every_resource_reason_maps_to_its_own_token_and_the_right_slot() {
    fn witness(reason: &ResourceReason) -> &'static str {
        match reason {
            ResourceReason::Heartbeats { .. } => "Heartbeats",
            ResourceReason::ExecutionSteps => "ExecutionSteps",
            ResourceReason::RecursionDepth { .. } => "RecursionDepth",
            ResourceReason::Cancelled => "Cancelled",
            ResourceReason::Memory { .. } => "Memory",
            ResourceReason::StructuralBudget { .. } => "StructuralBudget",
        }
    }

    const OBSERVED: u64 = 900;
    // Which slot each reason's observed value belongs in. `Steps` means the u64
    // field carries it and the depth field is zero; `Depth` is the mirror image;
    // `Neither` means the reason carries no number through this triple at all.
    #[derive(Clone, Copy, PartialEq, Debug)]
    enum Slot {
        Steps,
        Depth,
        Neither,
    }

    let cases: Vec<(ResourceReason, &str, Slot)> = vec![
        (
            ResourceReason::Heartbeats {
                consumed: OBSERVED,
                limit: 64,
            },
            "inconclusive:Heartbeats",
            Slot::Steps,
        ),
        (
            ResourceReason::ExecutionSteps,
            "inconclusive:Steps",
            Slot::Steps,
        ),
        (
            ResourceReason::RecursionDepth { limit: 64 },
            "inconclusive:Depth",
            Slot::Depth,
        ),
        (
            ResourceReason::Cancelled,
            "inconclusive:Cancelled",
            Slot::Neither,
        ),
        (
            ResourceReason::Memory { limit_bytes: 64 },
            "inconclusive:Memory",
            Slot::Steps,
        ),
        (
            ResourceReason::StructuralBudget {
                unit: StructuralUnit::InputBytes,
            },
            "inconclusive:StructuralBudget:InputBytes",
            Slot::Neither,
        ),
    ];

    // THE LIST COVERS EVERY VARIANT. `witness` cannot compile if a variant is
    // added without an arm, and this count cannot pass if one is added without a
    // case -- so the two together are what make the hand-written list total.
    let covered = cases
        .iter()
        .map(|(reason, _, _)| witness(reason))
        .collect::<BTreeSet<_>>();
    assert_eq!(
        covered.len(),
        6,
        "a `ResourceReason` variant has no case here. `witness` names {covered:?}; add the \
         missing one with its token and its slot rather than widening this number"
    );

    let mut tokens = BTreeSet::new();
    for (reason, expected_token, slot) in cases {
        let name = witness(&reason);
        let usage = ResourceUsage {
            reason,
            allowed: 64,
            observed: OBSERVED,
        };
        let (token, steps, depth) = resource_usage_facts(&usage);

        assert_eq!(
            token, expected_token,
            "`{name}` must file itself as `{expected_token}`"
        );
        assert!(
            tokens.insert(token.clone()),
            "`{name}` reuses the token `{token}`. Two reasons sharing one token collapse into a \
             single census family: the counts still balance, and every exhaustion of one cause is \
             attributed to the other"
        );
        // BOUND TO THE SHAPE AND DIRECTION RULES -- NOT to membership in a
        // closed set, and the previous wording here said otherwise. This comment
        // read "bound to the closed family taxonomy", which overstates what the
        // call proves: `check_family_token` refuses an empty name, a `,` or `=`
        // that would make a census row re-read as a different family, a
        // non-`rejected:` token in the restrictive direction and a `rejected:`
        // or `accepted` token in the non-answer one. It has no list of known
        // families, so `banana` passes here. Closure over the tokens a RUN can
        // emit lives in
        // `every_family_token_a_run_can_emit_belongs_to_the_closed_taxonomy`,
        // which sorts them into four prefix shapes -- a different check, in a
        // different place, and the one to read if you want to know what the
        // taxonomy admits.
        check_family_token(&token, FamilyDirection::NoAnswer)
            .unwrap_or_else(|reason| panic!("`{name}` emits an illegal family token: {reason}"));

        let observed_slot = match (steps, depth) {
            (0, 0) => Slot::Neither,
            (s, 0) if s == OBSERVED => Slot::Steps,
            (0, d) if u64::from(d) == OBSERVED => Slot::Depth,
            other => panic!(
                "`{name}` reported {other:?}, which is neither the observed value in one slot nor \
                 zero in both"
            ),
        };
        assert_eq!(
            observed_slot, slot,
            "`{name}` put its observed value in the wrong slot: {steps} step(s), depth {depth}. A \
             depth exhaustion filed as steps is a well-formed row with a plausible number and the \
             wrong cause"
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
    // AND THE INTERVENING WORD IS NOT A CONTRACTION, SO IT NEEDS A NEEDLE.
    // "does not YET exist" is the same retracted claim and no expansion reaches
    // it; nor does "has not been built". Measured with rg before adding: zero
    // occurrences of any of these in the scanned documents, so the population is
    // empty and the plants below are the whole of it.
    const STALE: [&str; 6] = [
        "unbuilt",
        "does not exist",
        "is not built",
        "not built yet",
        "does not yet exist",
        "has not been built",
    ];
    // R4 asks for the cadence STATED WHERE THE CLAIM IS MADE, so this is checked per claim
    // site, not per document. The first version checked per document and a planted mutant
    // survived it: stripping the cadence from the B4 bullet left the reader of that bullet
    // with a bare per-commit claim, while a paragraph 340 lines away kept the document
    // green. Same wrong-scope shape as fln-8zsq's first guard, one artifact up.
    // Both spellings, because `on-demand` does not contain `on demand` and the mutant that
    // taught me the first lesson also slipped past on the hyphen.
    const CADENCE: [&str; 3] = ["shortfall", "on demand", "on-demand"];
    // THE SCAN DECIDES PER LINE, SO A WRAPPED CLAIM IS STATED BY NEITHER HALF.
    // Demonstrated on synthetic documents rather than on the real ones, because
    // at this commit no site in either file is hidden: an empty population needs
    // a planted member or the rule below is unfalsifiable.
    assert_eq!(
        claim_sites_hidden_by_a_line_break("the matrix runs {1, 8,\n32} threads\n"),
        1,
        "a claim split across a line break must be counted as hidden, or the rule below cannot \
         fire"
    );
    assert_eq!(
        claim_sites_hidden_by_a_line_break("a {1, 8, 32} claim\n"),
        0,
        "an ordinary statement must not be reported as hidden"
    );
    // AND A WRAP IS NOT THE ONLY WAY TO HIDE ONE -- A WRAP PLUS A SPELLING IS.
    // Measured before this cell: the needle was the literal `{1, 8, 32}`, so a
    // claim that was BOTH re-spaced AND wrapped scored zero here and zero at the
    // per-line scan, which is a join neither half of the guard could see. The
    // real documents carry no such site today (all three score zero hidden), so
    // this synthetic member is the whole population and the measurement that
    // separates the rules is: old 0, new 1.
    assert_eq!(
        claim_sites_hidden_by_a_line_break("the matrix runs {1,8,\n32} threads\n"),
        1,
        "a claim both re-spaced and wrapped is invisible to the per-line scan too, so it must \
         count as hidden -- matching a literal needle here made the two halves of this guard \
         recognise different claims"
    );
    // AND STRIPPING WHITESPACE MUST NOT MANUFACTURE A CLAIM. Deleting spaces
    // joins neighbouring text, so a table cell could in principle be read as a
    // statement nobody made; the intervening characters are what stop it.
    assert_eq!(
        claim_sites_hidden_by_a_line_break("| {1,8 | 32} |\n"),
        0,
        "whitespace-insensitive counting must not join unrelated text into a claim"
    );
    // AND A LINE STATING IT TWICE IS NOT A HIDDEN SITE. This control exists
    // because my first measurement of the real documents compared lines
    // CONTAINING the phrase against OCCURRENCES of it and reported two hidden
    // sites that do not exist.
    assert_eq!(
        claim_sites_hidden_by_a_line_break("{1, 8, 32} and {1, 8, 32}\n"),
        0,
        "two statements on one line are both visible to a per-line scan; counting lines instead \
         of occurrences is what makes them look hidden"
    );

    // THE STALE SCAN IS PER-LINE TOO, and it wants a CONJUNCTION: a line must
    // both mention the matrix and call it missing. Split across a break, neither
    // half does. Synthetic, because no pair in either document straddles one
    // today -- measured -- so an empty population needs a planted member.
    assert_eq!(
        stale_claim_split_across_lines("the corpus-scale matrix\ndoes not exist yet\n", &STALE),
        Some(1),
        "a stale claim split across a break must be found, or the rule below cannot fire"
    );
    // AND A PAIR IS NOT THE WIDEST A SENTENCE WRAPS. Measured against the rule
    // this replaces: old None, new Some(1). Neither the pair scan nor the
    // per-line scan could see a claim wrapped over three lines.
    assert_eq!(
        stale_claim_split_across_lines("the corpus-scale matrix\ndoes\nnot exist yet\n", &STALE),
        Some(1),
        "a stale claim wrapped over three lines is stated by no line and by no pair, so a scan \
         bounded at two lines reports green on a document that still carries it"
    );
    // AND THE WIDENING MUST STOP AT A PARAGRAPH BREAK. This control is against
    // my own fix: deleting the blank-line bound makes this input report Some(1),
    // and makes AGENTS.md:1155 report Some(1) too, where a sentence naming the
    // matrix and a phrase from the stale list sit in DIFFERENT paragraphs.
    assert_eq!(
        stale_claim_split_across_lines("the matrix is fine\n\nthe corpus does not exist\n", &STALE),
        None,
        "two paragraphs are not one wrapped sentence; joining across a blank line is how this \
         scan starts inventing sites that nobody wrote"
    );
    assert_eq!(
        stale_claim_split_across_lines("the matrix does not exist\nand that is that\n", &STALE),
        None,
        "a line that states both belongs to the per-line rule; reporting it here would blame the \
         wrong line for a claim that one line already makes"
    );

    // THE DOCUMENT LIST IS HAND-WRITTEN, AND A HAND-LISTED SCOPE ROTS. Measured
    // over every tracked markdown file: the claim also appears TWICE in
    // COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md -- the document
    // AGENTS.md calls the single source of truth -- and both sites name neither
    // a scope nor a cadence. The guard below has never read that file, so those
    // two statements have never been checked by the thing that exists to check
    // them.
    //
    // They are recorded here rather than repaired: this test may only change
    // itself. The allowance is ONE-WAY. A new unqualified site in any top-level
    // document reddens; repairing one of these two does NOT, because the check
    // is `<=` per document rather than an equality. An allowance that reddened a
    // correct repair would be a wall, not a ledger.
    // A QUALIFIER ALONE IS NOT ENOUGH, and the previous version counted as
    // though it were. Synthetic, because both live sites name neither.
    assert_eq!(
        unscoped_claim_sites(
            "the Prelude matrix runs {1, 8, 32}\n",
            &QUALIFIERS,
            &CADENCE
        ),
        1,
        "a site naming its scope but not the cadence must still count, or the derived scope is \
         weaker than the list it extends"
    );
    assert_eq!(
        unscoped_claim_sites(
            "the Prelude matrix runs {1, 8, 32} on demand\n",
            &QUALIFIERS,
            &CADENCE
        ),
        0,
        "a site naming both must not count, or the rule refuses honest lines"
    );
    // A SPELLING MUST NOT HIDE A CLAIM.
    assert!(
        states_thread_matrix_claim("across {1,8,32} threads per commit"),
        "the unspaced spelling must be recognised, or the plan's PG-5 gate row stays invisible"
    );
    // AND NEITHER MAY A SPELLING WITH NO BRACES. This assertion used to read
    // `!states_thread_matrix_claim`, pinning a narrowness that WAS the escape: a
    // document could state the claim in prose, name no scope, and be seen by
    // nothing. Flipping a control is worth saying out loud -- the old one was
    // not wrong about false joins, it was wrong about which risk was larger.
    assert!(
        states_thread_matrix_claim("compared at 1, 8 and 32 threads per commit"),
        "a claim spelled in prose is still the claim, and naming no scope is exactly how it \
         would have escaped"
    );
    assert!(
        states_thread_matrix_claim("at 1, 8, and 32 threads"),
        "an Oxford comma is a spelling, not a different claim"
    );
    // AND SO MUST THE QUALIFIER BE NEAR THE CLAIM. A claim line in these
    // documents is a whole paragraph -- AGENTS.md:316 is 3359 collapsed
    // characters -- so asking whether the LINE mentions the corpus asks almost
    // nothing. Measured against the rule this replaces: old counts this site
    // qualified, new counts it unscoped.
    let distant = format!(
        "the matrix runs {{1, 8, 32}} per commit.{} It is a corpus observation, an on-demand \
         shortfall.",
        " padding".repeat(120)
    );
    assert_eq!(
        unscoped_claim_sites(&distant, &QUALIFIERS, &CADENCE),
        1,
        "a qualifier 1000 characters away in a different sentence does not state the scope of \
         this claim; R4 asks for it where the claim is made"
    );
    // AND THE SAME SENTENCE MUST STILL PASS. The control against my own bound:
    // every real qualified site sits within 70 collapsed characters of its
    // claim, and a rule that reddens those invents sites instead of missing them.
    assert_eq!(
        unscoped_claim_sites(
            "the matrix runs {1, 8, 32} over the corpus, an on-demand shortfall",
            &QUALIFIERS,
            &CADENCE
        ),
        0,
        "a qualifier in the sentence that states the claim must still count, or the bound \
         reddens every honest site"
    );
    // AND SO IS A CAPITAL LETTER. The anchor tested `contains("matrix")`, so a
    // sentence opening with the subject named a subject the rule did not
    // recognise. Measured against the rule this replaces: invisible, now caught.
    for cased in [
        "Matrix runs are unbuilt\n",
        "The corpus-scale Matrix does not exist\n",
        "The corpus-scale matrix Doesn't exist\n",
    ] {
        let scanned = stale_scan_form(cased);
        assert!(
            scanned.contains("matrix") && STALE.iter().any(|stale| scanned.contains(stale)),
            "a retracted description is the same false statement whichever letters it \
             capitalises: {cased}"
        );
    }
    // AND THE ORDER OF THE TWO NORMALISATIONS IS THE WHOLE OF THAT LAST CASE.
    // The expansion matches lowercase, so expanding first and lowercasing after
    // leaves "Doesn't exist" untouched by both halves.
    assert!(
        !contractions_expanded("The corpus-scale matrix Doesn't exist").contains("does not exist"),
        "this is the pipeline that misses it, pinned so the order is not swapped back by \
         someone reading the two steps as interchangeable"
    );
    assert!(
        stale_scan_form("The corpus-scale matrix Doesn't exist").contains("does not exist"),
        "and this is the order that catches it: lowercase, then expand"
    );
    // A WRAP IS NOT A DISAGREEMENT, AND AN EXACT COUNT IS STILL AN EXACT COUNT.
    // The marker check compares whitespace-free forms, so reflowing the sentence
    // cannot redden it. Measured against the rule this replaces: the wrapped
    // form was false, which is a guard reddening over a claim nobody changed.
    let marker_now = "observations recorded: 1, latest observed 2026-07-26";
    let wrapped_doc =
        "the corpus lane has observations recorded: 1, latest\nobserved 2026-07-26 at the pin\n";
    assert!(
        !wrapped_doc.contains(marker_now),
        "this is the reading that reddens: a raw `contains` cannot see a phrase across a line \
         break, and a reflow is not an edit to the claim"
    );
    assert!(
        whitespace_free(wrapped_doc).contains(&whitespace_free(marker_now)),
        "and this is the reading that does not: the document says exactly what the receipt says"
    );
    // AND THE CONTROL AGAINST THAT WIDENING: THE NUMBERS STILL HAVE TO MATCH.
    for disagreeing in [
        "observations recorded: 2, latest observed 2026-07-26",
        "observations recorded: 1, latest observed 2026-07-27",
    ] {
        assert!(
            !whitespace_free(wrapped_doc).contains(&whitespace_free(disagreeing)),
            "ignoring whitespace must not make a different count or a different date read as \
             the same marker: {disagreeing}"
        );
    }
    // A CONTRACTION IS A SPELLING, AND THE STALE RULE WAS WRITTEN AGAINST ONE
    // WORDING. Measured against the rule this replaces: each of these was
    // invisible, and each is the natural way to write the retracted claim.
    for missed in [
        "the corpus-scale matrix doesn't exist\nand that is that\n",
        "the corpus-scale matrix does not yet exist\nand that is that\n",
        "the corpus-scale matrix has not been built\nand that is that\n",
    ] {
        assert!(
            contractions_expanded(missed).contains("matrix")
                && STALE
                    .iter()
                    .any(|stale| contractions_expanded(missed).contains(stale)),
            "a retracted description spelled with a contraction or an intervening word is the \
             same false statement, and a literal needle list walks past it: {missed}"
        );
    }
    // AND THE TYPOGRAPHIC APOSTROPHE IS THE ONE AN EDITOR INSERTS UNASKED.
    assert!(
        contractions_expanded("the matrix doesn\u{2019}t exist").contains("does not exist"),
        "a curly apostrophe must normalise like a straight one, or the rule depends on which \
         editor wrote the sentence"
    );
    // AND THE CONTROL AGAINST THE WIDENING: A TRUE STATEMENT MUST STAY CLEAN.
    assert!(
        !STALE.iter().any(|stale| {
            contractions_expanded("the corpus-scale matrix exists and has been run once")
                .contains(stale)
        }),
        "the sentence the documents actually carry must not become a stale description; this \
         widening must refuse wordings, not facts"
    );
    // AND THE TWO RULES OF THE ALLOWANCE TIER MUST BE READ TOGETHER. This input
    // is the whole point of the assertion above: the site count is ZERO while a
    // claim is plainly present, because it is wrapped. A tier that reads only
    // the count sees an unblemished document.
    let wrapped_and_unqualified = "the matrix runs {1, 8,\n32} threads per commit\n";
    assert_eq!(
        unscoped_claim_sites(wrapped_and_unqualified, &QUALIFIERS, &CADENCE),
        0,
        "a wrapped claim is stated by neither half, so the per-line count cannot see it -- this \
         is the reading that makes the document look clean"
    );
    assert_eq!(
        claim_sites_hidden_by_a_line_break(wrapped_and_unqualified),
        1,
        "and the hidden-site rule must see exactly what the count cannot, or nothing in the \
         allowance tier distinguishes this document from one that never made the claim"
    );
    // AND THE STRICT TIER MUST NOT BE WEAKER THAN THE LENIENT ONE. The scanned
    // documents are checked with no allowance at all, and they were still asked
    // only whether the LINE mentions a qualifier -- so the tier that forgives
    // three known sites was applying a rule the tier that forgives nothing did
    // not. Measured at the five real qualified sites: qualifier within 70
    // collapsed characters, cadence within 318, on lines up to 3359, so both
    // tiers stay green on every one of them.
    //
    // The two are asserted to AGREE here rather than merely to exist, because
    // agreeing today is what they did before drifting twice.
    assert_eq!(
        unscoped_claim_sites(&distant, &QUALIFIERS, &CADENCE) == 0,
        qualifier_is_near_the_claim(&distant, &QUALIFIERS, NEARBY_QUALIFIER)
            && qualifier_is_near_the_claim(&distant, &CADENCE, NEARBY_QUALIFIER),
        "the allowance tier and the scanned tier must reach the same verdict on the same line, \
         or a claim refused where three are forgiven passes where none are"
    );
    assert!(
        !qualifier_is_near_the_claim(&distant, &QUALIFIERS, NEARBY_QUALIFIER),
        "a qualifier 1000 characters away must not satisfy the scanned tier either; it was the \
         weaker of the two and it is the one with no allowance"
    );
    assert!(
        qualifier_is_near_the_claim(
            "the matrix runs {1, 8, 32} over the corpus, an on-demand shortfall",
            &QUALIFIERS,
            NEARBY_QUALIFIER
        ),
        "a qualifier in the sentence stating the claim must satisfy the scanned tier, or every \
         honest site in AGENTS.md reddens"
    );
    // AND THE NOUN MUST BE NEAR THE NUMERALS. This decoy is invisible to every
    // per-line scan and visible only to the whole-document one, so the guard
    // reports a wrapped claim site that nobody wrote. Measured against the rule
    // this replaces: whole-segment 1 hidden, local 0.
    let unrelated = format!(
        "see sections 1, 8 and 32 of the plan\n{}\nthe matrix runs on threads\n",
        "filler ".repeat(20)
    );
    assert_eq!(
        claim_sites_hidden_by_a_line_break(&unrelated),
        0,
        "a list naming those three numbers is not a claim just because the DOCUMENT mentions \
         threads somewhere else; a guard that invents a site is worse than one that misses it"
    );
    // AND THE WINDOW IS TAKEN ON CHAR BOUNDARIES. Measured: a byte window panics
    // here, inside the em dash, and AGENTS.md is full of them.
    assert_eq!(
        thread_matrix_claim_count(&format!("\u{2014}{} 1, 8 and 32 threads", "a".repeat(38))),
        1,
        "the neighbourhood window must not split a multi-byte character; a panicking guard is an \
         invariant failure, not a diagnostic"
    );
    // AND THE BOUND THAT REPLACES IT: THE NUMBERS ALONE ARE NOT A CLAIM. This is
    // the control against my own widening -- without the "thread" requirement,
    // any list naming those three numbers becomes a determinism claim.
    assert!(
        !states_thread_matrix_claim("see sections 1, 8 and 32 of the plan"),
        "three numbers in a list are not a statement about thread counts; a widening that reads \
         them as one invents sites nobody wrote"
    );
    // THE SCOPE STOPPED AT THE ROOT, AND DEPTH IS A DIRECTION IT WAS NEVER
    // DERIVED IN. Measured on the real repository: root-only sees 10 documents,
    // this walk sees 23, and the three that state the claim are the same three,
    // so the scope widens by thirteen files without a verdict moving.
    let scope_root = Path::new(env!("CARGO_TARGET_TMPDIR")).join("t6r7-scope-walk-v1");
    for relative in [
        "root.md",
        "docs/nested.md",
        "docs/deeper/still.md",
        "target/built.md",
        "vendor/upstream.md",
        ".hidden/scratch.md",
        "._droppings.md",
        "docs/._droppings.md",
    ] {
        let path = scope_root.join(relative);
        fs::create_dir_all(path.parent().expect("a fixture entry has a parent"))
            .expect("the scope fixture tree must be creatable");
        fs::write(&path, b"").expect("a scope fixture document must be writable");
    }
    let walked = markdown_documents_below(&scope_root)
        .into_iter()
        .map(|path| {
            path.strip_prefix(&scope_root)
                .expect("a walked path lies below the fixture root")
                .to_string_lossy()
                .into_owned()
        })
        .collect::<Vec<_>>();
    assert_eq!(
        walked,
        vec![
            "docs/deeper/still.md".to_string(),
            "docs/nested.md".to_string(),
            "root.md".to_string()
        ],
        "the walk must descend into ordinary directories, refuse build output, vendored text and \
         every dotted NAME whether file or directory, and report a sorted order that does not \
         depend on the filesystem"
    );

    // THREE, NOT TWO, AND THE THIRD WAS ALWAYS THERE. Raising a ledger is the
    // direction that hides rot, so the reason is recorded: the count rose
    // because the matcher stopped missing `{1,8,32}`, not because a new site
    // appeared. It is the PG-5 gate row, which says "per commit" and names no
    // scope -- the strongest place the unqualified claim could sit.
    const UNSCANNED_ALLOWANCE: [(&str, usize); 1] =
        [("COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md", 3)];
    // AND THE KEY IS THE PATH, NOT THE FILE NAME. Two documents may share a name
    // once the walk goes below the root, and an allowance keyed by name would
    // then answer for a file it was never written about.
    let documents = markdown_documents_below(&repo);
    assert!(
        documents
            .iter()
            .any(|path| path.ends_with("crates/fln-kernel/tests/REFERENCE_DIFFERENTIAL.md")),
        "the walk must reach documents below the root on the REAL repository, not only in the \
         fixture: a cell that passes on a synthetic tree proves the rule fires, not that this \
         scope covers anything"
    );
    // AND AN ALLOWANCE ROW MUST NAME A DOCUMENT THE WALK ACTUALLY REACHES. The
    // ledger is keyed by relative path and consulted with a lookup that FALLS
    // BACK TO ZERO when nothing matches, so a row whose document is renamed,
    // moved below a skipped directory, or deleted goes quietly dead: the lookup
    // misses, the allowance silently becomes 0, and the failure that follows
    // names the document rather than the stale row. Every direction of that rot
    // reads as a fault in the file being scanned.
    //
    // What is NOT asserted, deliberately: that the count still matches what the
    // document carries. `unqualified <= allowed` is one-way on purpose -- an
    // equality would redden the correct repair of any of the three sites, which
    // is a wall rather than a ledger. This checks that the row has a subject,
    // not that its subject is unchanged.
    let names_a_scanned_document = |doc: &str| {
        documents.iter().any(|path| {
            path.strip_prefix(&repo)
                .map(|relative| relative.to_string_lossy() == doc)
                .unwrap_or(false)
        })
    };
    for (doc, count) in UNSCANNED_ALLOWANCE {
        assert!(
            names_a_scanned_document(doc),
            "the allowance ledger forgives {count} unqualified claim site(s) in {doc}, and the \
             walk does not reach that path: the row is dead, its subject is scanned with an \
             allowance of zero, and the failure would name the document instead of this row"
        );
        assert!(
            count > 0,
            "{doc} carries a zero allowance row, which is what every unlisted document already \
             gets; a row that forgives nothing records nothing"
        );
    }
    // AND THE PREDICATE MUST BE ABLE TO SAY NO. A lookup that answered true for
    // everything would pass the loop above without reading the ledger at all.
    assert!(
        !names_a_scanned_document("COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md.moved"),
        "the scope check must refuse a path the walk does not reach, or it is not checking \
         anything"
    );
    assert!(
        !documents
            .iter()
            .any(|path| path.components().any(|part| part.as_os_str() == "vendor")),
        "vendored upstream markdown must stay out of the scope, or this guard reports on Lean's \
         prose as though we had written it"
    );
    for document in SCANNED_DOCUMENTS {
        assert!(
            names_a_scanned_document(document),
            "{document} is read line by line by the strict tier and skipped by the allowance \
             tier, and the walk does not reach it: no tier examines it and every count below \
             still balances"
        );
    }
    let in_scope = documents.len();
    let mut skipped = 0usize;
    let mut examined = 0usize;
    for path in documents {
        let name = path
            .strip_prefix(&repo)
            .unwrap_or(&path)
            .to_string_lossy()
            .into_owned();
        if SCANNED_DOCUMENTS.contains(&name.as_str()) {
            skipped += 1;
            continue;
        }
        examined += 1;
        let Ok(text) = fs::read_to_string(&path) else {
            continue;
        };
        // BOTH HALVES, AS THE SCANNED PATH REQUIRES. This counted only sites
        // missing a QUALIFIER, while a scanned document must name its scope AND
        // the corpus lane's cadence. A site carrying `Prelude` but no cadence
        // therefore dropped out of the count and met neither rule -- a gap
        // between the two paths, opened by the commit that derived this scope.
        let unqualified = unscoped_claim_sites(&text, &QUALIFIERS, &CADENCE);
        // AND A WRAPPED CLAIM CONSUMES NO ALLOWANCE, WHICH IS HOW A LEDGER READS
        // CLEAN. The count above decides per line, so a claim split across a
        // line break is stated by neither half, counts zero, and this document
        // passes with its allowance untouched -- indistinguishable from a
        // document that never made the claim. The scanned tier has been checked
        // for this since the day the rule existed; the tier that ALLOWS sites
        // never was, so the hole sat in the half where a site is permitted
        // rather than forbidden. Measured across all 23 documents in scope:
        // zero hidden sites today, so this asserts a property that holds and
        // guards one that could stop holding silently.
        assert_eq!(
            claim_sites_hidden_by_a_line_break(&text),
            0,
            "{name} states the {{1, 8, 32}} determinism claim across a line break, where this \
             count decides per line: neither half states it, so the site consumes no allowance \
             and the document reads exactly like one that never made the claim"
        );
        let allowed = UNSCANNED_ALLOWANCE
            .iter()
            .find(|(doc, _)| *doc == name)
            .map_or(0, |(_, count)| *count);
        assert!(
            unqualified <= allowed,
            "{name} states the {{1, 8, 32}} determinism claim {unqualified} time(s) without \
             naming its scope, and this guard does not read that file. Allowance is {allowed}. \
             Either qualify the claim there or add the document to the list below so it is \
             checked like the others"
        );
    }

    // EVERY DOCUMENT IN SCOPE IS READ BY EXACTLY ONE TIER. A document skipped
    // here on the belief that the strict tier reads it, while the strict tier
    // reads a different list, is examined by nothing at all and shows up in no
    // count -- the failure is silence rather than a wrong number.
    assert_eq!(
        skipped + examined,
        in_scope,
        "{in_scope} markdown documents are in scope, {skipped} were skipped as strictly scanned \
         and {examined} were examined against the allowance: every document must be read by \
         exactly one tier"
    );
    assert_eq!(
        skipped,
        SCANNED_DOCUMENTS.len(),
        "the allowance tier skipped {skipped} documents while {} are declared strictly scanned; \
         a document skipped by one tier and not read by the other is checked by nothing",
        SCANNED_DOCUMENTS.len()
    );

    let mut checked = 0usize;
    for doc in SCANNED_DOCUMENTS {
        let text = fs::read_to_string(repo.join(doc))
            .unwrap_or_else(|error| panic!("{doc} must be readable: {error}"));
        assert_eq!(
            stale_claim_split_across_lines(&text, &STALE),
            None,
            "{doc} calls the corpus-scale matrix missing across a line break, where the stale \
             scan needs both halves on one line: neither half states it, so the document keeps a \
             retracted description while this guard reports green"
        );
        assert_eq!(
            claim_sites_hidden_by_a_line_break(&text),
            0,
            "{doc} states the {{1, 8, 32}} claim across a line break, where this scan decides per \
             line: neither half states it, so no half is required to name its scope and the \
             claim stands unqualified while this guard reports green"
        );
        for (index, line) in text.lines().enumerate() {
            let expanded = stale_scan_form(line);
            if expanded.contains("matrix") {
                for stale in STALE {
                    assert!(
                        !expanded.contains(stale),
                        "{doc}:{} still describes the corpus-scale matrix as missing, but it \
                         exists and has been run (R2 of fln-corpus-thread-matrix-93te). A \
                         stale qualifier is a false statement in the other direction:\n  {line}",
                        index + 1
                    );
                }
            }
            // THE SAME MATCHER THE DERIVED SCOPE USES. This loop tested the
            // literal `{1, 8, 32}` while the scope beside it stripped
            // whitespace, so the two paths recognised different claims: a
            // scanned document could have spelled it `{1,8,32}` and stated it
            // without a scope, exactly as the plan's PG-5 gate row does, and
            // this loop would have walked past it. Measured at this commit,
            // neither scanned document uses a variant -- so nothing was hidden
            // here yet, and the swap changes no count today.
            if !states_thread_matrix_claim(line) {
                continue;
            }
            checked += 1;
            assert!(
                qualifier_is_near_the_claim(line, &QUALIFIERS, NEARBY_QUALIFIER),
                "{doc}:{} states the {{1, 8, 32}} determinism claim without naming its \
                 scope, while the per-commit matrix's input is the Prelude and the \
                 corpus-scale matrix is an on-demand lane that gates nothing. A reader \
                 takes this as covering the corpus per commit (beads fln-8zsq, \
                 fln-corpus-thread-matrix-93te):\n  {line}",
                index + 1
            );
            assert!(
                qualifier_is_near_the_claim(line, &CADENCE, NEARBY_QUALIFIER),
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

    // AND THE COUNT ONLY MEANS WHAT THE MARKER SAYS IF THE ROWS DESCRIBE ONE CORPUS.
    if let Some((index, foreign)) = first_foreign_corpus_revision(
        receipts
            .iter()
            .map(|receipt| receipt.corpus_fixture_hash.as_str()),
    ) {
        panic!(
            "{}:{}: this row observed corpus {foreign}, while the first row observed {}. Every              check on this file is per row, so both rows are individually valid and the marker              still counts them together as though they were repeated observations of ONE              corpus revision -- which is the reading that makes a count evidence at all. Two              corpora observed once each is not one corpus observed twice.
             
             Both honest actions: keep the receipts for a corpus revision in their own file,              or re-derive the claim the documents make so it says what the rows actually              show. Neither is editing this assertion.",
            path.display(),
            index + 1,
            receipts
                .first()
                .map_or("nothing", |receipt| receipt.corpus_fixture_hash.as_str())
        );
    }
    // AND TWO ROWS MAY NOT CLAIM THE SAME OBSERVATION INSTANT.
    if let Some((index, instant)) =
        first_repeated_observation_instant(receipts.iter().map(|receipt| receipt.observed_unix_s))
    {
        panic!(
            "{}:{}: this row records observed_unix_s {instant}, which an earlier row already              records. The lane takes about 32 minutes, so two genuine runs cannot share an              instant: this is one observation retained twice, and the marker counts it as two              -- the count is the whole of what makes it evidence.
             
             Both honest actions: drop the duplicated line, or, if these really are distinct              runs, give each the instant it actually finished at.",
            path.display(),
            index + 1
        );
    }
    assert_eq!(first_repeated_observation_instant([]), None);
    assert_eq!(first_repeated_observation_instant([7]), None);
    assert_eq!(first_repeated_observation_instant([1, 2, 3]), None);
    assert_eq!(
        first_repeated_observation_instant([5, 5]),
        Some((1, 5)),
        "an immediately duplicated instant must be found"
    );
    assert_eq!(
        first_repeated_observation_instant([1, 2, 1]),
        Some((2, 1)),
        "and so must one that repeats a row further back, which a rule comparing only \
         NEIGHBOURING rows would walk past"
    );

    // AND THE RULE MUST BE ABLE TO SAY BOTH THINGS. Planted because the file
    // holds one row: a rule over a one-element set agrees with every mutant.
    assert_eq!(first_foreign_corpus_revision([]), None);
    assert_eq!(first_foreign_corpus_revision(["a"]), None);
    assert_eq!(first_foreign_corpus_revision(["a", "a", "a"]), None);
    assert_eq!(
        first_foreign_corpus_revision(["a", "b"]),
        Some((1, "b")),
        "a second corpus revision must be found, and named by row"
    );
    assert_eq!(
        first_foreign_corpus_revision(["a", "a", "c"]),
        Some((2, "c")),
        "and it must be found after any number of agreeing rows, not only at the second"
    );

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
    for doc in SCANNED_DOCUMENTS {
        let doc_text = fs::read_to_string(repo.join(doc))
            .unwrap_or_else(|error| panic!("{doc} must be readable: {error}"));
        // COMPARED WITH THE WHITESPACE REMOVED, BECAUSE A HARD WRAP IS NOT A
        // DISAGREEMENT. The marker is a six-word phrase and this was a raw
        // `contains` over the file: reflow the paragraph so "latest" ends a line
        // and the document still says exactly what the receipt says, while this
        // guard reports that the documents and the evidence file disagree about
        // how much evidence exists. Both documents carry it unwrapped today --
        // measured, and `rg` finds no line ending mid-marker -- so nothing moves
        // now; the point is that an editor reflowing a paragraph must not be
        // able to redden a claim it did not change. Same reasoning, same
        // normalisation, as the claim scan two guards up.
        assert!(
            whitespace_free(&doc_text).contains(&whitespace_free(&marker)),
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

/// The first retained row describing a different corpus than the first one does.
///
/// A CROSS-ROW PROPERTY CANNOT BE EXPRESSED BY A PER-ROW VALIDATOR, and every
/// check on this file was per row: pin, widths, digest counts, unmatrixed
/// modules. Each row can be perfectly valid while the SET means something other
/// than what the marker says about it. The marker aggregates the rows into one
/// count, and this file's own comment gives that count its meaning -- "several
/// are repeated observations over one corpus revision, which is a different
/// (still not invariant) class". Repeated observations of ONE corpus is a
/// stronger reading than one observation each of two corpora, and the arithmetic
/// is identical: both are "observations recorded: 2".
///
/// Vacuous today at one retained row, which is exactly when a cross-row rule is
/// easiest to leave out and hardest to notice missing, so it is planted below
/// rather than demonstrated on the file.
///
/// Takes hashes rather than receipts so the plants are inputs instead of
/// fixtures: constructing a receipt to test this would test the constructor.
fn first_foreign_corpus_revision<'a>(
    hashes: impl IntoIterator<Item = &'a str>,
) -> Option<(usize, &'a str)> {
    let mut rows = hashes.into_iter().enumerate();
    let (_, first) = rows.next()?;
    rows.find(|(_, hash)| *hash != first)
}

/// The first retained row claiming an instant an earlier row already claimed.
///
/// The second cross-row property, and the one the marker is most exposed to. A
/// duplicated line -- appended twice, or carried twice by a merge -- is one run
/// recorded two times, and the count cannot tell that from two runs: the marker
/// reads "observations recorded: 2, latest observed <the same date>", which is
/// how a single 32-minute observation becomes two.
///
/// The instant is the right key. Two genuine runs of a lane that takes half an
/// hour cannot finish in the same second, so a repeat is a duplicate or a
/// fabrication, and either way the count overstates the evidence. Comparing
/// whole rows would miss the more likely accident, where a hand edit changes one
/// timing field while the run behind it stays the same.
///
/// Order-independent by construction, because `latest_observation` already
/// treats row order as the lane's append order and nothing else.
fn first_repeated_observation_instant(
    instants: impl IntoIterator<Item = u64>,
) -> Option<(usize, u64)> {
    let mut seen: Vec<u64> = Vec::new();
    for (index, instant) in instants.into_iter().enumerate() {
        if seen.contains(&instant) {
            return Some((index, instant));
        }
        seen.push(instant);
    }
    None
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
            "a corpus revision named rather than digested",
            CorpusMatrixReceipt {
                corpus_fixture_hash: "mathlib-v4.32.0".to_string(),
                ..real.clone()
            },
            "not a 64-character lowercase hex digest",
        ),
        (
            "a digest one character short",
            CorpusMatrixReceipt {
                corpus_fixture_hash: real.corpus_fixture_hash[..63].to_string(),
                ..real.clone()
            },
            "not a 64-character lowercase hex digest",
        ),
        (
            "the right digest in the wrong case",
            CorpusMatrixReceipt {
                corpus_fixture_hash: real.corpus_fixture_hash.to_ascii_uppercase(),
                ..real.clone()
            },
            "not a 64-character lowercase hex digest",
        ),
        (
            "no producing source named",
            CorpusMatrixReceipt {
                lane_source_digest_at_run: String::new(),
                ..real.clone()
            },
            "empty lane_source_digest_at_run",
        ),
        (
            "a producing source named rather than digested",
            CorpusMatrixReceipt {
                lane_source_digest_at_run: "the-corpus-matrix-lane".to_string(),
                ..real.clone()
            },
            "not a 64-character lowercase hex digest",
        ),
        (
            "a producing source digest in the wrong case",
            CorpusMatrixReceipt {
                lane_source_digest_at_run: real.lane_source_digest_at_run.to_ascii_uppercase(),
                ..real.clone()
            },
            "not a 64-character lowercase hex digest",
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
        // Added by `franken_lean-t6r7`: this loop has the same shape as the
        // whole-Mathlib receipt's, and `contains("")` is always true, so an
        // empty expectation would silently reduce a cell to `is_err()`. Purely
        // additive -- it refuses nothing this test accepted before unless an
        // expectation is genuinely empty.
        assert!(
            !expected.is_empty(),
            "mutant `{mutation}` carries an empty expectation, which matches every message"
        );
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
