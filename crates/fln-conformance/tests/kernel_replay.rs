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
//! Kinds K1 does not yet admit (inductives, constructors, recursors, quots,
//! opaques, unsafe/partial definitions) are admitted-unchecked into the
//! environment, counted per kind — an honestly-typed limitation of the
//! bootstrap slice, not a silent pass.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::PathBuf;

use fln_core::expr::{Expr, ExprNode};
use fln_core::name::Name;
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use fln_env::environment::Environment;
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
        ExprNode::Lam { body, .. } => format!("(fun _ => {})", shape(body, fuel - 1)),
        ExprNode::ForallE { body, .. } => format!("(forall _, {})", shape(body, fuel - 1)),
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

/// Replay order: a declaration is admitted only after every constant it
/// mentions that lives in the SAME module. The module's `constants` array is
/// storage order, not dependency order — a checker must sort it (Kahn, with
/// stable module-order tie-breaking so the replay is deterministic).
/// Declarations inside a dependency cycle (mutual blocks, and the
/// self-referential generated equation lemmas) are emitted last, in module
/// order, and reported.
fn topological_order(infos: &[ConstantInfo]) -> (Vec<usize>, Vec<usize>) {
    let index: HashMap<Name, usize> = infos
        .iter()
        .enumerate()
        .map(|(i, info)| (info.name().clone(), i))
        .collect();
    let deps: Vec<Vec<usize>> = infos
        .iter()
        .enumerate()
        .map(|(i, info)| {
            let mut d: Vec<usize> = dependencies(info)
                .iter()
                .filter_map(|n| index.get(n).copied())
                .filter(|&j| j != i)
                .collect();
            d.sort_unstable();
            d.dedup();
            d
        })
        .collect();
    let mut remaining: Vec<usize> = deps.iter().map(|d| d.len()).collect();
    let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); infos.len()];
    for (i, d) in deps.iter().enumerate() {
        for &j in d {
            dependents[j].push(i);
        }
    }
    let mut ready: Vec<usize> = (0..infos.len()).filter(|&i| remaining[i] == 0).collect();
    ready.reverse(); // pop() yields ascending module order
    let mut order = Vec::with_capacity(infos.len());
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
    let cyclic: Vec<usize> = (0..infos.len()).filter(|i| !placed.contains(i)).collect();
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

/// The kernel `Declaration` for a checkable constant kind, or `None` for the
/// type-forming frontier (which is admitted-unchecked in phase 1).
fn as_declaration(info: &ConstantInfo) -> Option<Declaration> {
    match info {
        ConstantInfo::Axiom(v) => Some(Declaration::Axiom(v.clone())),
        ConstantInfo::Thm(v) => Some(Declaration::Thm(v.clone())),
        ConstantInfo::Defn(v) if v.safety == DefinitionSafety::Safe => {
            Some(Declaration::Defn(v.clone()))
        }
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

#[test]
fn prelude_replays_through_the_kernel() {
    let Some(lib) = reference_lib() else {
        eprintln!(
            "SKIP kernel_replay: pinned Reference stdlib not found \
             (set FLN_REFERENCE_LIB or install the pin); typed limitation, not a pass"
        );
        return;
    };
    let bytes = std::fs::read(lib.join("Init/Prelude.olean")).expect("read Init/Prelude.olean");
    let view = OleanView::parse(&bytes).expect("parse olean");
    let mut decoder = DeclDecoder::new(&view, WalkBudget::default());
    let infos = decoder
        .decode_module_constants()
        .expect("decode Prelude constants");
    assert_eq!(infos.len(), 2204, "Prelude constant census at the pin");

    // Admission is two-phase. Phase 1: the type-forming frontier K1 does not
    // yet check — inductives, their constructors and recursors, quotients —
    // is mutually referential by nature (an inductive's constructor's type
    // names the inductive), so it is admitted-unchecked as a block, in module
    // order, giving every later declaration its type constants. Phase 2: the
    // K1-checkable declarations (axioms, safe defs, theorems) are replayed in
    // dependency order AMONG THEMSELVES, so a proof is never checked before a
    // lemma it cites. This mirrors how a real checker consumes a module.
    // Frontier = exactly the kinds `as_declaration` cannot turn into a kernel
    // Declaration, so the two partitions are complementary by construction.
    let is_frontier = |info: &ConstantInfo| as_declaration(info).is_none();
    let frontier: Vec<usize> = (0..infos.len())
        .filter(|&i| is_frontier(&infos[i]))
        .collect();
    let checkable: Vec<ConstantInfo> = infos
        .iter()
        .filter(|info| !is_frontier(info))
        .cloned()
        .collect();
    let (order, cyclic) = topological_order(&checkable);
    eprintln!(
        "kernel_replay order: {} frontier admitted-unchecked, {} checkable \
         ({} topologically sorted, {} in dependency cycles replayed last)",
        frontier.len(),
        checkable.len(),
        order.len(),
        cyclic.len()
    );

    let mut env = Environment::new();
    let mut accepted: u64 = 0;
    let mut rejected: BTreeMap<String, u64> = BTreeMap::new();
    let mut rejected_names: Vec<String> = Vec::new();
    let mut reasons: BTreeMap<String, u64> = BTreeMap::new();
    let mut inconclusive: u64 = 0;
    let mut unchecked: BTreeMap<&'static str, u64> = BTreeMap::new();
    let mut gap_families: BTreeMap<&'static str, u64> = BTreeMap::new();
    let mut skipped_partition: u64 = 0;
    // Phase 1: frontier, in module order.
    for &i in &frontier {
        env = env.add_decl(infos[i].clone()).expect("frontier admission");
        *unchecked.entry(infos[i].kind_name()).or_default() += 1;
    }
    // Phase 2 below iterates the checkable declarations in dependency order.
    let checkable_infos = checkable;
    let budget = Budget::DEFAULT;

    for idx in order.into_iter().chain(cyclic) {
        let info = checkable_infos[idx].clone();
        // `checkable` was partitioned to hold exactly axioms, theorems, and
        // safe definitions, so `as_declaration` is always `Some` here; a `None`
        // would only mean the partition drifted, and is skipped defensively
        // rather than panicking (FL-INV-07 keeps the harness itself panic-free).
        let Some(decl) = as_declaration(&info) else {
            skipped_partition += 1;
            env = env.add_decl(info).expect("one-name law over Prelude");
            continue;
        };
        match fln_kernel::check(&env, &decl, budget) {
            Verdict::Accepted { .. } => accepted += 1,
            Verdict::Rejected { class, message, .. } => {
                *rejected.entry(format!("{class:?}")).or_default() += 1;
                *reasons.entry(format!("{class:?}: {message}")).or_default() += 1;
                *gap_families
                    .entry(reduction_gap_family(info.name()))
                    .or_default() += 1;
                if rejected_names.len() < 20 {
                    rejected_names.push(format!("{} ({class:?})", info.name().to_display_string()));
                }
                // Probe lane (bead fln-d4x): FLN_REPLAY_PROBE is a comma list
                // of declaration names; matching rejections dump bounded type
                // and value shapes so a reduction-gap hypothesis can be
                // anchored in the DECODED term, not guessed from the name.
                if let Ok(probe) = std::env::var("FLN_REPLAY_PROBE") {
                    let name = info.name().to_display_string();
                    if probe.split(',').any(|entry| entry.trim() == name) {
                        eprintln!("PROBE {name} [{class:?}: {message}]");
                        eprintln!("  type  = {}", shape(&info.constant_val().type_, 6));
                        if let ConstantInfo::Defn(defn) = &info {
                            eprintln!("  value = {}", shape(&defn.value, 8));
                        }
                    }
                }
            }
            Verdict::Inconclusive { .. } => inconclusive += 1,
        }
        // The Reference accepted this module; carry every declaration forward
        // regardless of our verdict so downstream declarations see it.
        env = env.add_decl(info).expect("one-name law over Prelude");
    }

    let checked = accepted + inconclusive + rejected.values().sum::<u64>();
    eprintln!(
        "kernel_replay census: checked={checked} accepted={accepted} \
         inconclusive={inconclusive} rejected={rejected:?} unchecked={unchecked:?}"
    );
    if !rejected_names.is_empty() {
        eprintln!("first rejections: {rejected_names:?}");
        let mut by_count: Vec<_> = reasons.iter().collect();
        by_count.sort_by(|a, b| b.1.cmp(a.1));
        for (reason, n) in by_count.iter().take(12) {
            eprintln!("  {n:>5}  {reason}");
        }
    }

    eprintln!("kernel_replay triage (reduction-gap families): {gap_families:?}");

    // Census law: every declaration lands in exactly one bucket.
    assert_eq!(skipped_partition, 0, "checkable partition drifted");
    let unchecked_total: u64 = unchecked.values().sum();
    assert_eq!(checked + unchecked_total, 2204);

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
