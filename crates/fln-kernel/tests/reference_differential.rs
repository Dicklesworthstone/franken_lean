//! Differential conformance harness: fln-kernel verdicts against the PINNED
//! Reference kernel (`leanprover/lean4` v4.32.0), bead franken_lean-bc7 / §18.
//!
//! AGENTS.md makes this a standing Tribunal obligation: "Kernel verdicts diffed
//! against the Reference kernel ... Any pairwise disagreement is a finding;
//! kernel divergence blocks release." Everything else in `tests/` asserts what
//! *we* think a rule says. This file is the only place that asks the Reference.
//!
//! # The oracle is executed, not asserted
//!
//! Each case carries real Lean source. The pinned `lean` binary runs it and its
//! verdict is read off the process — no expectation is hard-coded for the
//! Reference side. That is the whole point: an expectation I wrote would just be
//! my belief about the pin restated, and my belief is the thing under test.
//!
//! Classifying that verdict needs care, and getting it wrong would silently
//! invert the harness. Probing the pin first showed why: a perfectly well-typed
//! `def f : A := a` over an axiom exits NON-ZERO, because the code generator
//! refuses a noncomputable body. Exit status alone would have recorded a clean
//! acceptance as a rejection and then "agreed" with us for the wrong reason.
//! So [`OracleVerdict`] classifies by diagnostic rather than by exit status.
//!
//! My first classifier was still wrong, and the corpus caught it: it treated
//! *any* tagged `error(lean.…)` as a non-verdict, which silently swallowed
//! `error(lean.unknownIdentifier)` — a genuine refusal of the declaration.
//! The rule that shipped is narrower and stated as data: a short allowlist of
//! compiler-stage tags (today only `lean.dependsOnNoncomputable`) is refused as
//! [`OracleVerdict::NotAVerdict`], and every other diagnostic, tagged or not,
//! is a rejection. Both spellings — `error:` and `error(tag):` — count.
//!
//! # The asymmetry (D23) is structural here, not a convention
//!
//! The two directions of disagreement are NOT equivalent and the comparator
//! does not treat them as such:
//!
//! * **We accept, the Reference rejects.** Unsoundness. We would admit a
//!   declaration the trusted checker refuses. Release-blocking, never
//!   carve-out-able, and [`Divergence::classify`] has no path that excuses it.
//! * **We reject, the Reference accepts.** Incompleteness. Still a finding, but
//!   this is the *only* direction where D23's "soundness beats bug-parity"
//!   carve-out can apply, and only through an explicit [`CARVE_OUTS`] row naming
//!   the case and its justification.
//!
//! `CARVE_OUTS` is empty. It is a list, not a mechanism to reach for: an entry
//! is a public statement that we knowingly diverge from the pin.
//!
//! # Scope, stated plainly
//!
//! **This is RULE-SHAPE coverage, not CORPUS coverage.** The generator crosses
//! sorts, binders and admission kinds, which says nothing about whether the
//! pinned stdlib agrees with us. That is bead `fln-lst4`: it needs decoded
//! `.olean` declarations, therefore `fln-olean`, therefore `fln-conformance`,
//! and it is the harder and more valuable half. Nobody should read a growing
//! case count here as the Corpus obligation being discharged.
//!
//! For the same reason, two numbers that get quoted together are worth keeping
//! apart. `fln-conformance`'s `kernel_replay` reports `checked=2198`, and those
//! 2198 declarations are ONE module (`Init.Prelude`) — that is the differential's
//! real corpus coverage today. The 158,608 constants across 2433 modules it also
//! reports are a DECODE cross-check: evidence that we can read what the Reference
//! wrote, not that our kernel and its kernel agree on a verdict.
//!
//! Cases are GENERATED rather than hand-paired. Each is described once and both
//! halves are derived from that description, because the old arrangement — a
//! Lean text and a `Declaration` written side by side — had a failure mode worse
//! than being wrong: a transcription slip made a case VACUOUS. The halves stopped
//! describing the same declaration, both sides still answered, they still agreed,
//! and the case proved nothing while looking green. [`Ty`] and [`Tm`] can only be
//! built by constructors that produce the Lean rendering and the `Expr` in one
//! call, so the two cannot drift.
//!
//! Scaling past hand-pairing means decoding real `.olean` declarations, which
//! needs `fln-olean` — outside fln-kernel's `allow-direct` covenant (fln-core,
//! fln-hash, fln-bignum, fln-env). That work belongs in `fln-conformance`,
//! which already owns the replay path, and this file does not pretend to it.
//!
//! Absent toolchain is a typed SKIP, never a silent pass: RCH workers do not
//! carry the pin, so this must run locally.

#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::scratch::{REFDIFF_PREFIX, ScratchRoot};
use fln_env::constants::{
    AxiomVal, ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, TheoremVal,
};
use fln_env::environment::Environment;
use fln_kernel::verdict::{Budget, RejectClass, Verdict};
use fln_kernel::{Declaration, check};
use std::path::PathBuf;
use std::process::Command;

// ---------------------------------------------------------------------------
// Provenance
// ---------------------------------------------------------------------------

/// The pin this harness is a differential against. Hard-coded rather than
/// discovered so that a machine with a *different* toolchain on PATH cannot
/// quietly produce oracle verdicts from the wrong Reference.
const PIN_TAG: &str = "leanprover--lean4---v4.32.0";

fn pinned_lean() -> Option<PathBuf> {
    let path = PathBuf::from(std::env::var("HOME").ok()?)
        .join(".elan/toolchains")
        .join(PIN_TAG)
        .join("bin/lean");
    path.is_file().then_some(path)
}

// ---------------------------------------------------------------------------
// The oracle
// ---------------------------------------------------------------------------

/// What the Reference said about a source text.
#[derive(Debug, Clone, PartialEq, Eq)]
enum OracleVerdict {
    /// Clean exit: the Reference admitted every declaration in the text.
    Accepted,
    /// The Reference refused a declaration, with its first diagnostic line.
    Rejected(String),
    /// The run failed for a reason that is NOT a judgment about the
    /// declaration — today, a tagged `error(lean.…)` such as the codegen
    /// family. Never folded into Accepted or Rejected; the case is refused.
    NotAVerdict(String),
}

/// Run the pinned Reference over `source` and classify what it said.
fn ask_reference(lean: &PathBuf, case_id: &str, source: &str) -> OracleVerdict {
    // Guard-owned oracle workspace: reclaimed when the case passes, retained when it
    // fails (franken_lean-eir2). The guard's pid/stamp/serial naming also repairs the
    // old `fln-refdiff-{case_id}` collision between two concurrent test processes.
    let dir = ScratchRoot::create(REFDIFF_PREFIX, "reference-differential", case_id)
        .expect("create oracle workspace");
    let file = dir.join("Case.lean");
    std::fs::write(&file, source).expect("write oracle source");

    let out = Command::new(lean)
        .arg(&file)
        .output()
        .expect("the pinned Reference must be executable");
    let merged = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );

    // Not every TAGGED error is a non-verdict, and assuming so was wrong: the
    // first draft of this classifier refused `error(lean.unknownIdentifier)`,
    // which IS a refusal of the declaration, and the corpus caught it by
    // reporting a case as unscorable. So the non-verdict set is an explicit
    // allowlist of compiler-stage complaints rather than "anything tagged".
    //
    // `dependsOnNoncomputable` is the one that matters: it fires on a
    // perfectly well-typed declaration whose body cannot be compiled, and
    // reading it as a rejection would invert the harness.
    const NON_VERDICT_TAGS: &[&str] = &["lean.dependsOnNoncomputable"];
    if let Some(line) = merged
        .lines()
        .find(|l| NON_VERDICT_TAGS.iter().any(|t| l.contains(t)))
    {
        return OracleVerdict::NotAVerdict(line.trim().to_string());
    }
    // Everything else that reports an error is a refusal of the declaration.
    // Both spellings must be caught: the pin writes plain `error:` for core
    // judgments and `error(tag):` for classified ones, and matching only the
    // former silently dropped `unknownIdentifier` into "no diagnostic".
    match merged
        .lines()
        .find(|l| l.contains("error:") || l.contains("error("))
    {
        Some(line) => OracleVerdict::Rejected(line.trim().to_string()),
        None if out.status.success() => OracleVerdict::Accepted,
        None => OracleVerdict::NotAVerdict(format!(
            "non-zero exit with no diagnostic: {:?}",
            out.status
        )),
    }
}

// ---------------------------------------------------------------------------
// The subject
// ---------------------------------------------------------------------------

fn n(s: &str) -> Name {
    Name::str(Name::anonymous(), s)
}
fn sort1() -> Expr {
    Expr::sort(Level::one())
}
fn prop() -> Expr {
    Expr::sort(Level::zero())
}
fn cst(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}
fn cval(name: &str, type_: Expr) -> ConstantVal {
    ConstantVal {
        name: n(name),
        level_params: vec![],
        type_,
    }
}

/// Extend `env` with an axiom, without going through `check` — the premises of
/// a case are setup, not subject. Mirrors the `axiom` lines of the source.
fn with_axiom(env: &Environment, name: &str, type_: Expr) -> Environment {
    env.add_decl(ConstantInfo::Axiom(AxiomVal {
        base: cval(name, type_),
        is_unsafe: false,
    }))
    .expect("premise adds")
}

fn defn(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Defn(DefinitionVal {
        base: cval(name, type_),
        value,
        hints: fln_env::constants::ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![n(name)],
    })
}

fn thm(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Thm(TheoremVal {
        base: cval(name, type_),
        value,
        all: vec![n(name)],
    })
}

/// A TYPE, carrying its Lean rendering and its `Expr` together.
///
/// This pairing is the whole point of the generator. Previously each case wrote
/// the Lean text and the `Expr` separately, and a slip between them did not make
/// the case wrong — it made it VACUOUS: the halves stopped describing the same
/// declaration, both sides still answered, they still agreed, and the case
/// proved nothing while looking green. Here a type can only be built by a
/// constructor that produces both halves in one call, so they cannot drift.
#[derive(Clone)]
struct Ty {
    lean: String,
    expr: Expr,
}

fn t_prop() -> Ty {
    Ty {
        lean: "Prop".into(),
        expr: prop(),
    }
}
fn t_type() -> Ty {
    Ty {
        lean: "Type".into(),
        expr: sort1(),
    }
}
fn t_type1() -> Ty {
    Ty {
        lean: "Type 1".into(),
        expr: Expr::sort(Level::succ(Level::one()).expect("Sort 2 packs")),
    }
}
fn t_named(name: &str) -> Ty {
    Ty {
        lean: name.to_string(),
        expr: cst(name),
    }
}
/// `a -> b`, non-dependent, so the body carries no loose bvar.
fn t_arrow(a: &Ty, b: &Ty) -> Ty {
    Ty {
        lean: format!("{} -> {}", a.lean, b.lean),
        expr: Expr::forall_e(n("x"), a.expr.clone(), b.expr.clone(), BinderInfo::Default),
    }
}

/// A TERM, paired with its Lean rendering for the same reason as [`Ty`].
#[derive(Clone)]
struct Tm {
    lean: String,
    expr: Expr,
}

fn m_const(name: &str) -> Tm {
    Tm {
        lean: name.to_string(),
        expr: cst(name),
    }
}
/// `fun (_ : ty) => body`, where `body` is closed — so no de Bruijn arithmetic
/// is needed and none can be got wrong.
fn m_lambda(ty: &Ty, body: &Tm) -> Tm {
    Tm {
        lean: format!("fun (_ : {}) => {}", ty.lean, body.lean),
        expr: Expr::lam(
            n("x"),
            ty.expr.clone(),
            body.expr.clone(),
            BinderInfo::Default,
        ),
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Axiom,
    Def,
    Theorem,
}

/// One differential case, described ONCE. Both the Lean source handed to the
/// Reference and the `Declaration` handed to our kernel are derived from these
/// fields, so the two halves are the same statement by construction.
struct Case {
    id: String,
    rule: &'static str,
    /// Axioms declared before the subject, in order.
    premises: Vec<(String, Ty)>,
    kind: Kind,
    name: String,
    ty: Ty,
    /// `None` for an axiom.
    body: Option<Tm>,
}

impl Case {
    /// The Lean text. `def` is emitted `noncomputable` because a body built
    /// from axioms has no executable content and the code generator would
    /// otherwise fail the file for a reason that is not a kernel verdict.
    fn source(&self) -> String {
        let mut out = String::new();
        for (name, ty) in &self.premises {
            out.push_str(&format!("axiom {name} : {}\n", ty.lean));
        }
        match (self.kind, &self.body) {
            (Kind::Axiom, _) => out.push_str(&format!("axiom {} : {}\n", self.name, self.ty.lean)),
            (Kind::Def, Some(b)) => out.push_str(&format!(
                "noncomputable def {} : {} := {}\n",
                self.name, self.ty.lean, b.lean
            )),
            (Kind::Theorem, Some(b)) => out.push_str(&format!(
                "theorem {} : {} := {}\n",
                self.name, self.ty.lean, b.lean
            )),
            (k, None) => {
                let _ = k;
                unreachable!("only an axiom may have no body")
            }
        }
        out
    }

    /// The same statement as a premise environment plus the subject.
    fn subject(&self) -> (Environment, Declaration) {
        let mut env = Environment::new();
        for (name, ty) in &self.premises {
            env = with_axiom(&env, name, ty.expr.clone());
        }
        let decl = match (self.kind, &self.body) {
            (Kind::Axiom, _) => Declaration::Axiom(AxiomVal {
                base: cval(&self.name, self.ty.expr.clone()),
                is_unsafe: false,
            }),
            (Kind::Def, Some(b)) => defn(&self.name, self.ty.expr.clone(), b.expr.clone()),
            (Kind::Theorem, Some(b)) => thm(&self.name, self.ty.expr.clone(), b.expr.clone()),
            (_, None) => unreachable!("only an axiom may have no body"),
        };
        (env, decl)
    }
}

/// The generated corpus.
///
/// RULE-SHAPE COVERAGE, NOT CORPUS COVERAGE. Generating cases over sorts,
/// binders and admission kinds says nothing about whether the pinned stdlib
/// agrees with us — that is bead fln-lst4, it needs decoded oleans, and it is
/// the harder and more valuable half. This makes the small corpus trustworthy
/// and cheap to extend; it does not make it big.
/// One axis of the matrix: a sort, tagged for case ids.
type SortAxis = (&'static str, fn() -> Ty);

fn corpus() -> Vec<Case> {
    let mut cases = Vec::new();
    let sorts: [SortAxis; 3] = [
        ("prop", t_prop as fn() -> Ty),
        ("type", t_type),
        ("type1", t_type1),
    ];

    // KR-972: a declaration whose type IS a sort admits, at every sort.
    for (tag, mk) in sorts {
        cases.push(Case {
            id: format!("GEN-ACC-sort-{tag}"),
            rule: "KR-972 a declaration type that is a sort admits",
            premises: vec![],
            kind: Kind::Axiom,
            name: format!("A_{tag}"),
            ty: mk(),
            body: None,
        });
    }

    // KR-972 negative: a type whose own type is NOT a sort must be refused.
    // `d : D` with `D : Sort n`, so the type expression `d` infers to `D`,
    // which is a constant and not a sort.
    for (tag, mk) in sorts {
        cases.push(Case {
            id: format!("GEN-REJ-nonsort-{tag}"),
            rule: "KR-972 a declaration type that is not a sort is refused",
            premises: vec![("D".into(), mk()), ("d".into(), t_named("D"))],
            kind: Kind::Axiom,
            name: format!("bad_{tag}"),
            ty: t_named("d"),
            body: None,
        });
    }

    // KR-974: a theorem's type must be a Prop, and its body must match it.
    // The Prop row accepts; the Type rows are the elimination of the same
    // shape one universe up and must be refused.
    for (tag, mk) in sorts {
        let carrier = mk();
        let accept = tag == "prop";
        cases.push(Case {
            id: format!("GEN-{}-thm-{tag}", if accept { "ACC" } else { "REJ" }),
            rule: "KR-974 a theorem type must be a proposition",
            premises: vec![("P".into(), carrier.clone()), ("hp".into(), t_named("P"))],
            kind: Kind::Theorem,
            name: format!("t_{tag}"),
            ty: t_named("P"),
            body: Some(m_const("hp")),
        });
    }

    // KR-974 bodies: a definition body must be defeq to the declared type,
    // at every sort — matching accepts, crossed rejects.
    for (tag, mk) in sorts {
        cases.push(Case {
            id: format!("GEN-ACC-def-match-{tag}"),
            rule: "KR-974 a definition body type matching its declared type",
            premises: vec![("A".into(), mk()), ("a".into(), t_named("A"))],
            kind: Kind::Def,
            name: format!("f_{tag}"),
            ty: t_named("A"),
            body: Some(m_const("a")),
        });
        cases.push(Case {
            id: format!("GEN-REJ-def-mismatch-{tag}"),
            rule: "KR-974 a definition body type that is not the declared type",
            premises: vec![
                ("A".into(), mk()),
                ("B".into(), mk()),
                ("a".into(), t_named("A")),
            ],
            kind: Kind::Def,
            name: format!("g_{tag}"),
            ty: t_named("B"),
            body: Some(m_const("a")),
        });
    }

    // KR-105: a reference to a constant that is not in the environment.
    cases.push(Case {
        id: "GEN-REJ-unknown-const".into(),
        rule: "KR-105 a reference to a constant not in the environment",
        premises: vec![("A".into(), t_type())],
        kind: Kind::Def,
        name: "h".into(),
        ty: t_named("A"),
        body: Some(m_const("nope")),
    });

    // KR-107: a binder whose domain is a TERM rather than a type.
    cases.push(Case {
        id: "GEN-REJ-binder-domain".into(),
        rule: "KR-107 a binder domain that is not a type",
        premises: vec![("A".into(), t_type()), ("a".into(), t_named("A"))],
        kind: Kind::Def,
        name: "k".into(),
        ty: t_type(),
        body: None,
    });
    // …expressed as a definition whose declared type is the bad Pi.
    let last = cases.len() - 1;
    cases[last].ty = t_arrow(&t_named("a"), &t_named("A"));
    cases[last].kind = Kind::Axiom;

    // Function types at every sort, and a lambda inhabiting one: the binder
    // congruence path that carries a real domain on both sides.
    for (tag, mk) in sorts {
        let carrier = mk();
        cases.push(Case {
            id: format!("GEN-ACC-arrow-{tag}"),
            rule: "KR-107/KR-974 a function type inhabited by a lambda",
            premises: vec![("A".into(), carrier.clone()), ("a".into(), t_named("A"))],
            kind: Kind::Def,
            name: format!("fn_{tag}"),
            ty: t_arrow(&t_named("A"), &t_named("A")),
            body: Some(m_lambda(&t_named("A"), &m_const("a"))),
        });
        cases.push(Case {
            id: format!("GEN-REJ-arrow-domain-{tag}"),
            rule: "KR-302 a binder whose DOMAIN differs is not defeq",
            premises: vec![
                ("A".into(), carrier.clone()),
                ("B".into(), carrier.clone()),
                ("a".into(), t_named("A")),
            ],
            kind: Kind::Def,
            name: format!("fx_{tag}"),
            ty: t_arrow(&t_named("B"), &t_named("A")),
            body: Some(m_lambda(&t_named("A"), &m_const("a"))),
        });
    }

    cases
}

/// Our verdict, reduced to the axis the Reference also speaks on.
#[derive(Debug, Clone, PartialEq, Eq)]
enum OurVerdict {
    Accepted,
    Rejected(RejectClass),
    /// Not an answer (FL-INV-07). Never compared against an oracle verdict —
    /// a non-answer agrees with nothing.
    NonAuthoritative(String),
}

fn ask_ourselves(env: &Environment, decl: &Declaration) -> OurVerdict {
    match check(env, decl, Budget::DEFAULT) {
        fln_core::outcome::Outcome::Complete(Verdict::Accepted { .. }) => OurVerdict::Accepted,
        fln_core::outcome::Outcome::Complete(Verdict::Rejected { class, .. }) => {
            OurVerdict::Rejected(class)
        }
        fln_core::outcome::Outcome::Inconclusive(i) => {
            OurVerdict::NonAuthoritative(format!("inconclusive: {:?}", i.cause))
        }
        fln_core::outcome::Outcome::InternalFault(f) => {
            OurVerdict::NonAuthoritative(format!("internal fault: {f:?}"))
        }
    }
}

// ---------------------------------------------------------------------------
// The comparator, and the asymmetry
// ---------------------------------------------------------------------------

/// A documented, justified divergence from the pin. D23 permits exactly one
/// shape: we REJECT what the Reference ACCEPTS, because accepting it would be
/// unsound. The reverse can never appear here.
struct CarveOut {
    case_id: &'static str,
    justification: &'static str,
}

/// Empty, deliberately. Every row is a public statement that FrankenLean
/// knowingly disagrees with the Reference.
const CARVE_OUTS: &[CarveOut] = &[];

#[derive(Debug, PartialEq, Eq)]
enum Divergence {
    /// Both sides gave the same answer on the accept/reject axis.
    Agree,
    /// WE ACCEPT WHAT THE REFERENCE REJECTS. Unsoundness; release-blocking.
    /// No carve-out reaches this arm.
    UnsoundlyPermissive { oracle: String },
    /// We reject what the Reference accepts. Incompleteness; a finding unless
    /// a CARVE_OUTS row justifies it.
    Restrictive { ours: RejectClass },
    /// We produced no answer at all where the Reference produced one.
    NoAnswer { ours: String },
}

impl Divergence {
    fn classify(oracle: &OracleVerdict, ours: &OurVerdict) -> Divergence {
        match (oracle, ours) {
            (OracleVerdict::Accepted, OurVerdict::Accepted) => Divergence::Agree,
            (OracleVerdict::Rejected(_), OurVerdict::Rejected(_)) => Divergence::Agree,
            (OracleVerdict::Rejected(o), OurVerdict::Accepted) => {
                Divergence::UnsoundlyPermissive { oracle: o.clone() }
            }
            (OracleVerdict::Accepted, OurVerdict::Rejected(c)) => {
                Divergence::Restrictive { ours: *c }
            }
            (_, OurVerdict::NonAuthoritative(s)) => Divergence::NoAnswer { ours: s.clone() },
            (OracleVerdict::NotAVerdict(s), _) => Divergence::NoAnswer { ours: s.clone() },
        }
    }
}

fn carve_out_for(case_id: &str) -> Option<&'static CarveOut> {
    CARVE_OUTS.iter().find(|c| c.case_id == case_id)
}

// ---------------------------------------------------------------------------
// The runs
// ---------------------------------------------------------------------------

/// Result of one case, kept so both the differential test and the
/// divergence-detection test can share the machinery.
struct Outcome1 {
    id: String,
    rule: &'static str,
    oracle: OracleVerdict,
    ours: OurVerdict,
    divergence: Divergence,
}

fn run_corpus(lean: &PathBuf, cases: &[Case]) -> Vec<Outcome1> {
    cases
        .iter()
        .map(|case| {
            let oracle = ask_reference(lean, &case.id, &case.source());
            let (env, decl) = case.subject();
            let ours = ask_ourselves(&env, &decl);
            let divergence = Divergence::classify(&oracle, &ours);
            Outcome1 {
                id: case.id.clone(),
                rule: case.rule,
                oracle,
                ours,
                divergence,
            }
        })
        .collect()
}

/// The obligation itself: every case must agree, with the D23 asymmetry.
#[test]
fn kernel_verdicts_agree_with_the_pinned_reference() {
    let Some(lean) = pinned_lean() else {
        eprintln!(
            "SKIP (typed limitation): pinned Reference {PIN_TAG} absent; \
             this differential must run locally, not on an RCH worker"
        );
        return;
    };

    let cases = corpus();
    let results = run_corpus(&lean, &cases);
    let mut findings: Vec<String> = Vec::new();

    for r in &results {
        // Line-oriented, so a CI reader can diff runs.
        println!(
            "refdiff id={} rule=\"{}\" oracle={:?} ours={:?} verdict={:?}",
            r.id, r.rule, r.oracle, r.ours, r.divergence
        );
        match &r.divergence {
            Divergence::Agree => {}
            Divergence::UnsoundlyPermissive { oracle } => findings.push(format!(
                "{}: RELEASE-BLOCKING. We ACCEPT what the Reference REJECTS. \
                 Reference said: {oracle}. No carve-out can excuse this direction \
                 (D23 permits soundness over bug-parity, never the reverse).",
                r.id
            )),
            Divergence::Restrictive { ours } => match carve_out_for(&r.id) {
                Some(c) => println!(
                    "refdiff id={} CARVE-OUT accepted: {}",
                    r.id, c.justification
                ),
                None => findings.push(format!(
                    "{}: we reject ({ours:?}) what the Reference accepts. \
                     Incompleteness. Add a justified CARVE_OUTS row only if \
                     accepting it would be unsound; otherwise this is a defect.",
                    r.id
                )),
            },
            Divergence::NoAnswer { ours } => findings.push(format!(
                "{}: no comparable answer ({ours}). A non-answer agrees with \
                 nothing; the case cannot be scored.",
                r.id
            )),
        }
    }

    // THE REPORT IS THE CLAIM. A count, not a boolean: "differential testing
    // exists" is exactly the unquantified marketing AGENTS.md forbids.
    let accepts = results
        .iter()
        .filter(|r| matches!(r.oracle, OracleVerdict::Accepted))
        .count();
    let rejects = results
        .iter()
        .filter(|r| matches!(r.oracle, OracleVerdict::Rejected(_)))
        .count();
    let rules: std::collections::BTreeSet<&str> = results.iter().map(|r| r.rule).collect();
    println!(
        "refdiff SUMMARY: {} descriptions -> {} cases ({} accept-direction, {} \
         reject-direction), {} divergences, {} distinct rule shapes. \
         RULE-SHAPE COVERAGE, NOT CORPUS COVERAGE.",
        cases.len(),
        results.len(),
        accepts,
        rejects,
        findings.len(),
        rules.len()
    );

    assert!(
        findings.is_empty(),
        "kernel diverged from the pinned Reference on {} case(s):\n  {}",
        findings.len(),
        findings.join("\n  ")
    );

    // Coverage floor: a harness that silently stopped running its corpus would
    // otherwise report a clean pass.
    assert_eq!(
        results.len(),
        cases.len(),
        "the corpus did not run to completion"
    );
    assert!(
        results
            .iter()
            .any(|r| matches!(r.oracle, OracleVerdict::Accepted)),
        "no case exercised the ACCEPT direction"
    );
    assert!(
        results
            .iter()
            .any(|r| matches!(r.oracle, OracleVerdict::Rejected(_))),
        "no case exercised the REJECT direction"
    );
    // Floor on the generator itself. A matrix that quietly stopped crossing its
    // axes would otherwise still report a clean pass, which is the failure this
    // whole rig is built to make impossible.
    assert!(
        results.len() >= 20,
        "the generated corpus collapsed to {} cases",
        results.len()
    );
    assert!(
        rules.len() >= 7,
        "the generated corpus covers only {} rule shapes",
        rules.len()
    );
}

/// The harness must FAIL when we are wrong. A differential that cannot detect
/// divergence is worth less than no differential, because it converts an
/// untested claim into a false one — the same mistake as a green suite over an
/// unguarded rule, one level up.
///
/// This plants a subject that deliberately contradicts its own source: the
/// source is `REF-REJ-001`, which the Reference refuses because a theorem's type
/// must be a proposition, while the paired declaration is the well-formed
/// `REF-ACC-002` theorem that our kernel accepts. Whatever the pin says, our
/// side now answers ACCEPT to a text the Reference REJECTS, which is exactly the
/// release-blocking direction.
#[test]
fn harness_detects_divergence_when_our_side_is_broken() {
    let Some(lean) = pinned_lean() else {
        eprintln!("SKIP (typed limitation): pinned Reference {PIN_TAG} absent");
        return;
    };

    // A mismatched Case can no longer be CONSTRUCTED — source and subject are
    // both derived from one description, which is the property this generator
    // exists to provide. So the control composes the two halves by hand at the
    // call site instead: the Reference is asked about a text it must reject,
    // and our kernel is asked about a DIFFERENT, well-formed declaration it
    // must accept. That is the release-blocking direction, assembled
    // deliberately rather than by a slip.
    let rejected_source = "axiom A : Type\naxiom a : A\ntheorem bad : A := a\n";
    let oracle = ask_reference(&lean, "control-broken", rejected_source);

    let env = with_axiom(&Environment::new(), "P", prop());
    let env = with_axiom(&env, "hp", cst("P"));
    let ours = ask_ourselves(&env, &thm("t", cst("P"), cst("hp")));

    let divergence = Divergence::classify(&oracle, &ours);

    // Matched on the diagnostic text, not the whole line: the line carries an
    // absolute temp path, and pinning that would make the control fail on any
    // other machine for a reason having nothing to do with the kernel.
    assert!(
        matches!(&oracle, OracleVerdict::Rejected(m) if m.contains("is not a proposition")),
        "the oracle must actually reject this source, or the control proves \
         nothing; got {oracle:?}"
    );
    assert_eq!(ours, OurVerdict::Accepted, "our planted side must accept");
    assert!(
        matches!(divergence, Divergence::UnsoundlyPermissive { .. }),
        "the comparator must classify accept-over-reject as RELEASE-BLOCKING, \
         got {divergence:?}"
    );
    // And it must be unexcusable: no carve-out exists, and none could.
    assert!(
        carve_out_for("control-broken").is_none(),
        "the unsound direction must not be carve-out-able"
    );
}

/// The oracle's own classifier is load-bearing and was nearly wrong: a
/// noncomputable `def` over an axiom exits non-zero on a CODEGEN error while
/// being perfectly well-typed. Exit status alone would have scored that as a
/// rejection and then "agreed" with a broken kernel for the wrong reason.
#[test]
fn oracle_does_not_mistake_a_codegen_error_for_a_kernel_verdict() {
    let Some(lean) = pinned_lean() else {
        eprintln!("SKIP (typed limitation): pinned Reference {PIN_TAG} absent");
        return;
    };
    // Exactly REF-ACC-003 without `noncomputable`: well-typed, and the pin
    // still exits non-zero.
    let verdict = ask_reference(
        &lean,
        "oracle-codegen-probe",
        "axiom A : Type\naxiom a : A\ndef f : A := a\n",
    );
    assert!(
        matches!(verdict, OracleVerdict::NotAVerdict(_)),
        "a tagged codegen error must be refused as a non-verdict, not read as a \
         rejection; got {verdict:?}"
    );
}

/// `franken_lean-eir2` acceptance criterion 3: retention on failure is proved in BOTH
/// directions for this family, never inferred from the passing cell. This cell uses the
/// family's own constructor directly, so it does not need the pinned Reference to run.
#[test]
fn reference_differential_roots_reclaim_on_pass_and_retain_on_failure() {
    let passing = {
        let root = ScratchRoot::create(REFDIFF_PREFIX, "reference-differential", "reclaim-pass")
            .expect("create passing workspace");
        root.path().to_path_buf()
    };
    assert!(
        !passing.exists(),
        "a passing cell's oracle workspace must be reclaimed: {}",
        passing.display()
    );

    let observed = std::cell::RefCell::new(None);
    let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let root = ScratchRoot::create(REFDIFF_PREFIX, "reference-differential", "reclaim-fail")
            .expect("create failing workspace");
        *observed.borrow_mut() = Some(root.path().to_path_buf());
        panic!("deliberate failure so the fixture guard drops during an unwind");
    }));
    assert!(unwound.is_err(), "the failing cell must actually unwind");
    let retained = observed
        .into_inner()
        .expect("the failing cell materialized before it panicked");
    assert!(
        retained.exists(),
        "a failing cell's oracle workspace must be retained: {}",
        retained.display()
    );
    std::fs::remove_dir_all(&retained).expect("the probe reclaims what it retained");
}
