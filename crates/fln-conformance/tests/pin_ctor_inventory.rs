//! The pinned binary's own constructor inventories, asked at test time (bead
//! `fln-parity-ledger-l2-pinned-source-qydn`).
//!
//! # What this is for
//!
//! Four rows in `ci/PARITY_LEDGER.txt` (`:200-203`) record constructor inventories at level
//! **L2** with oracle-kind **pinned-source**. The ledger's own tier note (`:41-48`) defines
//! L2 as "the pinned Reference binary produced the expected value" and L1 as "implemented
//! against the pinned SOURCE semantics ... no Reference-produced value is compared". Those
//! four are earned by `crates/fln-core/tests/pin_inventory_census.rs`, which parses vendored
//! upstream `.lean` text — real evidence, and by the ledger's own definition L1, not L2.
//!
//! `qydn` recorded that the four had **no route**: "a constructor list has no printed
//! default in the sense an option does; walking the pin's environment for it is plausible
//! and untried, and is not claimed here." This is that walk. It is claimed here.
//!
//! The route is stock: an inductive's `ConstantInfo.inductInfo` carries `ctors : List Name`
//! in declaration order, and `Lean.Environment.find?` reaches it through ordinary
//! metaprogramming on an **unpatched** pin. No instrumented oracle, no §18.3 patched
//! Reference. That is the third surface bead `franken_lean-c24a`'s finding has now reached
//! — parse trees, the option registry, and now the environment's own inductive table.
//!
//! # Why the comparison is order-sensitive
//!
//! A constructor's *position* is its index, and the index is ABI- and olean-visible: it is
//! what a `.olean` stores and what `Expr.proj` counts against. Two inventories with the same
//! names in a different order are not the same inventory, so this compares sequences rather
//! than sets and reports the position of the first disagreement.
//!
//! # Why there is no fixture here, deliberately
//!
//! The oracle runs *in this test*, so there is no capture that can go stale between runs.
//! Bead `franken_lean-ext-observable-fixture-drift-gap-vqnu` records 28 rows resting on a
//! 533-record capture that nothing re-derives, one directory over; a live differential
//! cannot acquire that defect. The cost is a typed SKIP without the pinned toolchain, which
//! says in terms that nothing was established rather than passing quietly.
//!
//! # Relationship to the fln-core census, which is not superseded
//!
//! `pin_inventory_census.rs` compares the same inventories against vendored *source*. That
//! remains worth running: it is the check that the vendored tree matches what we implement,
//! and it runs where no toolchain is installed. This rig is the check that the *binary*
//! agrees, which is the one the ledger's L2 requires. Both sides derive our inventory by
//! exhaustive `match`, so adding a variant to any of these enums fails to compile in both
//! places rather than silently narrowing either comparison.

#![forbid(unsafe_code)]

use std::collections::BTreeMap;

use fln_conformance::pin;
use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level, LevelView};
use fln_core::name::{LeafView, Name};
use fln_core::options::{DataValue, KVMap};

// ---------------------------------------------------------------------------
// What this crate claims, derived by exhaustive match
// ---------------------------------------------------------------------------

/// One inductive whose constructor list is compared, and the ledger row it backs.
///
/// The `lean_type` field drives *both* the probe's target list and the comparison, so a
/// type cannot be dropped from the question while remaining in the answer — the join
/// AGENTS.md item 7 is about, kept inside one value.
struct Inventory {
    /// The pin's fully-qualified inductive.
    lean_type: &'static str,
    /// The `ci/PARITY_LEDGER.txt` symbol whose level this inventory earns.
    ledger_row: &'static str,
    /// Our constructors, in our declaration order.
    ours: fn() -> Vec<&'static str>,
}

/// The six inductives, against the four ledger rows they back.
///
/// `Literal` and `BinderInfo` are cited under `Lean.Expr.ctorInventory` because that row's
/// evidence names `vendor/lean4-src/src/Lean/Expr.lean`, which is where the pin declares
/// all three. Recorded as data rather than left implicit so the row a failure belongs to is
/// in the failure message.
const INVENTORIES: [Inventory; 6] = [
    Inventory {
        lean_type: "Lean.Name",
        ledger_row: "Lean.Name.ctorInventory",
        ours: our_name_ctors,
    },
    Inventory {
        lean_type: "Lean.Level",
        ledger_row: "Lean.Level.ctorInventory",
        ours: our_level_ctors,
    },
    Inventory {
        lean_type: "Lean.Expr",
        ledger_row: "Lean.Expr.ctorInventory",
        ours: our_expr_ctors,
    },
    Inventory {
        lean_type: "Lean.Literal",
        ledger_row: "Lean.Expr.ctorInventory",
        ours: our_literal_ctors,
    },
    Inventory {
        lean_type: "Lean.BinderInfo",
        ledger_row: "Lean.Expr.ctorInventory",
        ours: our_binder_info_ctors,
    },
    Inventory {
        lean_type: "Lean.DataValue",
        ledger_row: "Lean.DataValue.ctorInventory",
        ours: our_data_value_ctors,
    },
];

// Each of these constructs one value per arm and matches on it. The match is the point:
// adding a variant without adding it here fails to compile, so the list cannot silently
// stop covering the enum it claims to enumerate.

fn our_name_ctors() -> Vec<&'static str> {
    [
        Name::anonymous(),
        Name::str(Name::anonymous(), "s"),
        Name::num(Name::anonymous(), 0),
    ]
    .iter()
    .map(|name| match name.leaf_view() {
        LeafView::Anonymous => "anonymous",
        LeafView::Str(_) => "str",
        LeafView::Num(_) => "num",
    })
    .collect()
}

fn our_level_ctors() -> Vec<&'static str> {
    let param = Name::str(Name::anonymous(), "u");
    [
        Level::zero(),
        Level::zero().succ().expect("shallow"),
        Level::max(Level::zero(), Level::zero()).expect("shallow"),
        Level::imax(Level::zero(), Level::zero()).expect("shallow"),
        Level::param(param.clone()),
        Level::mvar(LMVarId(param)),
    ]
    .iter()
    .map(|level| match level.view() {
        LevelView::Zero => "zero",
        LevelView::Succ(_) => "succ",
        LevelView::Max(..) => "max",
        LevelView::IMax(..) => "imax",
        LevelView::Param(_) => "param",
        LevelView::MVar(_) => "mvar",
    })
    .collect()
}

fn our_expr_ctors() -> Vec<&'static str> {
    let param = Name::str(Name::anonymous(), "u");
    let leaf = Expr::bvar(0).expect("small");
    [
        Expr::bvar(0).expect("small"),
        Expr::fvar(FVarId(param.clone())),
        Expr::mvar(MVarId(param.clone())),
        Expr::sort(Level::zero()),
        Expr::const_(param.clone(), Vec::new()),
        Expr::app(leaf.clone(), leaf.clone()),
        Expr::lam(
            param.clone(),
            leaf.clone(),
            leaf.clone(),
            BinderInfo::Default,
        ),
        Expr::forall_e(
            param.clone(),
            leaf.clone(),
            leaf.clone(),
            BinderInfo::Default,
        ),
        Expr::let_e(
            param.clone(),
            leaf.clone(),
            leaf.clone(),
            leaf.clone(),
            false,
        ),
        Expr::lit(Literal::Nat(NatLit::from_u64(0))),
        Expr::mdata(KVMap::new(), leaf.clone()),
        Expr::proj(param, 0, leaf),
    ]
    .iter()
    .map(|expr| match expr.node() {
        ExprNode::BVar { .. } => "bvar",
        ExprNode::FVar { .. } => "fvar",
        ExprNode::MVar { .. } => "mvar",
        ExprNode::Sort { .. } => "sort",
        ExprNode::Const { .. } => "const",
        ExprNode::App { .. } => "app",
        ExprNode::Lam { .. } => "lam",
        ExprNode::ForallE { .. } => "forallE",
        ExprNode::LetE { .. } => "letE",
        ExprNode::Lit { .. } => "lit",
        ExprNode::MData { .. } => "mdata",
        ExprNode::Proj { .. } => "proj",
    })
    .collect()
}

fn our_literal_ctors() -> Vec<&'static str> {
    [
        Literal::Nat(NatLit::from_u64(0)),
        Literal::Str(String::new()),
    ]
    .iter()
    .map(|literal| match literal {
        Literal::Nat(_) => "natVal",
        Literal::Str(_) => "strVal",
    })
    .collect()
}

fn our_binder_info_ctors() -> Vec<&'static str> {
    [
        BinderInfo::Default,
        BinderInfo::Implicit,
        BinderInfo::StrictImplicit,
        BinderInfo::InstImplicit,
    ]
    .iter()
    .map(|info| match info {
        BinderInfo::Default => "default",
        BinderInfo::Implicit => "implicit",
        BinderInfo::StrictImplicit => "strictImplicit",
        BinderInfo::InstImplicit => "instImplicit",
    })
    .collect()
}

fn our_data_value_ctors() -> Vec<&'static str> {
    [
        DataValue::OfString(String::new()),
        DataValue::OfBool(false),
        DataValue::OfName(Name::str(Name::anonymous(), "u")),
        DataValue::OfNat(0),
        DataValue::OfInt(0),
        DataValue::OfSyntax(fln_core::options::SyntaxHandle(0)),
    ]
    .iter()
    .map(|value| match value {
        DataValue::OfString(_) => "ofString",
        DataValue::OfBool(_) => "ofBool",
        DataValue::OfName(_) => "ofName",
        DataValue::OfNat(_) => "ofNat",
        DataValue::OfInt(_) => "ofInt",
        DataValue::OfSyntax(_) => "ofSyntax",
    })
    .collect()
}

// ---------------------------------------------------------------------------
// The probe
// ---------------------------------------------------------------------------

/// `@TARGETS@` is substituted rather than `format!`-interpolated because the probe body is
/// full of `m!"{...}"` antiquotations, and brace-escaping a Lean program into a Rust format
/// string is a transcription hazard for no benefit.
///
/// `run_cmd` and `Environment.find?` are the pin's ordinary metaprogramming surface;
/// nothing here patches, links against, or executes upstream implementation code (D8). A
/// name that is absent, or present but not an inductive, is reported rather than skipped —
/// silence would be indistinguishable from agreement.
const PROBE_TEMPLATE: &str = r#"import Lean
open Lean
run_cmd do
  let env ← getEnv
  let targets : List Name := [@TARGETS@]
  for n in targets do
    match env.find? n with
    | some (.inductInfo info) =>
        for c in info.ctors do
          logInfo m!"CTOR|{n}|{c}"
    | some _ => logInfo m!"NOTINDUCTIVE|{n}"
    | none   => logInfo m!"MISSING|{n}"
  logInfo m!"PROBE_COMPLETE"
"#;

fn probe_source(types: &[&str]) -> String {
    let targets = types
        .iter()
        .map(|name| format!("`{name}"))
        .collect::<Vec<_>>()
        .join(", ");
    PROBE_TEMPLATE.replace("@TARGETS@", &targets)
}

/// What the pin answered: constructors per type in emission order, plus every type it could
/// not answer for, plus whether the probe ran to the end.
struct PinAnswer {
    ctors: BTreeMap<String, Vec<String>>,
    unanswerable: Vec<String>,
    complete: bool,
}

/// Marker-anchored rather than line-anchored: message rendering is not a contract this rig
/// wants to depend on, and a decoration change must not be reported as an inventory
/// divergence.
///
/// Constructor names arrive fully qualified (`Lean.Expr.bvar`); the type prefix is stripped
/// so the comparison is against the constructor name rather than against upstream's
/// namespacing. A name that does not carry the expected prefix is kept whole, so it shows up
/// as a divergence instead of being silently rewritten into agreement.
fn parse_answer(stdout: &str) -> PinAnswer {
    let mut ctors: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut unanswerable = Vec::new();
    let mut complete = false;
    for line in stdout.lines() {
        if let Some(rest) = line.split("CTOR|").nth(1) {
            let mut parts = rest.splitn(2, '|');
            if let (Some(ty), Some(ctor)) = (parts.next(), parts.next()) {
                let (ty, ctor) = (ty.trim(), ctor.trim());
                let short = ctor.strip_prefix(&format!("{ty}.")).unwrap_or(ctor);
                ctors.entry(ty.to_string()).or_default().push(short.into());
            }
        } else if let Some(rest) = line.split("NOTINDUCTIVE|").nth(1) {
            unanswerable.push(format!(
                "{}: the pin has a declaration by that name and it is not an inductive",
                rest.trim()
            ));
        } else if let Some(rest) = line.split("MISSING|").nth(1) {
            unanswerable.push(format!(
                "{}: the pin declares no constant by that name",
                rest.trim()
            ));
        } else if line.contains("PROBE_COMPLETE") {
            complete = true;
        }
    }
    PinAnswer {
        ctors,
        unanswerable,
        complete,
    }
}

// ---------------------------------------------------------------------------
// The comparison
// ---------------------------------------------------------------------------

/// Every way one inventory differs from the other, reported together and in position order.
///
/// A positional disagreement and a length disagreement are separate findings: the first is a
/// renamed or reordered constructor, the second is a constructor gained or lost. Collapsing
/// them would report a reorder as an addition and send the reader to the wrong repair.
fn divergences(lean_type: &str, row: &str, theirs: &[String], ours: &[&str]) -> Vec<String> {
    let mut out = Vec::new();
    for (i, (t, o)) in theirs.iter().zip(ours.iter()).enumerate() {
        if t != o {
            out.push(format!(
                "{lean_type} (row {row}): constructor {i} is `{t}` at the pin and `{o}` in \
                 fln-core — a renamed or reordered constructor moves its index, which is \
                 olean- and ABI-visible"
            ));
        }
    }
    if theirs.len() > ours.len() {
        out.push(format!(
            "{lean_type} (row {row}): the pin declares {} constructor(s) fln-core does not \
             implement: {}",
            theirs.len() - ours.len(),
            theirs[ours.len()..].join(", ")
        ));
    } else if ours.len() > theirs.len() {
        out.push(format!(
            "{lean_type} (row {row}): fln-core implements {} constructor(s) the pin does not \
             declare: {}",
            ours.len() - theirs.len(),
            ours[theirs.len()..].join(", ")
        ));
    }
    out
}

// ---------------------------------------------------------------------------
// The live differential
// ---------------------------------------------------------------------------

#[test]
fn every_constructor_inventory_fln_core_claims_is_the_one_the_pinned_binary_declares() {
    let Some(lean) = pin::pinned_lean() else {
        eprintln!("{}", pin::skip_notice("pin_ctor_inventory"));
        return;
    };

    let types: Vec<&str> = INVENTORIES.iter().map(|inv| inv.lean_type).collect();
    let answer = pin::ask(&lean, "pin_ctor_inventory", &probe_source(&types))
        .expect("the located pinned binary is executable");
    let parsed = parse_answer(&answer.stdout);

    assert!(
        answer.success,
        "the pinned binary refused the probe (exit {:?}).\nstdout:\n{}\nstderr:\n{}",
        answer.code, answer.stdout, answer.stderr
    );

    // A probe that died partway would leave the later types absent, and absence must not
    // read as agreement. The marker distinguishes "the pin does not have this type" from
    // "the probe never got that far".
    assert!(
        parsed.complete,
        "the probe did not run to completion, so every type it did not reach is unmeasured \
         rather than agreed.\nstdout:\n{}\nstderr:\n{}",
        answer.stdout, answer.stderr
    );
    assert!(
        parsed.unanswerable.is_empty(),
        "the pin could not answer for {} of the {} inventories:\n  {}",
        parsed.unanswerable.len(),
        INVENTORIES.len(),
        parsed.unanswerable.join("\n  ")
    );

    // The key set must be exactly what was asked. A type silently dropped from the answer
    // would make its comparison vacuous, which is the failure mode this whole bead is about.
    let answered: Vec<&str> = parsed.ctors.keys().map(String::as_str).collect();
    let mut expected = types.clone();
    expected.sort_unstable();
    assert_eq!(
        answered, expected,
        "the pin answered for a different set of inductives than the probe asked about"
    );

    let mut found = Vec::new();
    let mut compared = 0usize;
    for inv in &INVENTORIES {
        let theirs = &parsed.ctors[inv.lean_type];
        let ours = (inv.ours)();
        compared += ours.len();
        found.extend(divergences(inv.lean_type, inv.ledger_row, theirs, &ours));
    }
    assert!(
        found.is_empty(),
        "fln-core disagrees with the pinned binary about {} constructor(s):\n  {}",
        found.len(),
        found.join("\n  ")
    );

    // Reported, never asserted as coverage: this is a differential over OUR inventories, not
    // a census of the pin's inductive table.
    println!(
        "pin_ctor_inventory: {compared} constructors across {} inductives corroborated \
         against the pinned binary, backing the 4 ctorInventory rows of ci/PARITY_LEDGER.txt. \
         This is a differential over the inventories fln-core implements; it says nothing \
         about the rest of the pin's inductive table and is not a compatibility figure",
        INVENTORIES.len()
    );
}

// ---------------------------------------------------------------------------
// Planted violations — the comparison must be shown to fail
// ---------------------------------------------------------------------------

/// A differential that has only ever been observed agreeing is not evidence of agreement.
/// These drive the same `divergences` the live test does, so they run with or without the
/// pinned toolchain.
#[test]
fn the_comparison_catches_a_rename_a_reorder_a_gain_and_a_loss() {
    let ours = our_expr_ctors();
    let honest: Vec<String> = ours.iter().map(|c| (*c).to_string()).collect();
    assert!(
        divergences("Lean.Expr", "row", &honest, &ours).is_empty(),
        "an inventory that agrees must produce no findings, or the guard is a wall"
    );

    // 1. A constructor renamed upstream.
    let mut renamed = honest.clone();
    renamed[3] = "sorts".into();
    let found = divergences("Lean.Expr", "row", &renamed, &ours);
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(
        found[0].contains("constructor 3 is `sorts` at the pin and `sort` in fln-core"),
        "the finding must name the index and both spellings: {found:?}"
    );

    // 2. A reorder. Same names, different indexes — and the index is the ABI-visible part,
    //    so this must not be reported as agreement.
    let mut reordered = honest.clone();
    reordered.swap(0, 1);
    let found = divergences("Lean.Expr", "row", &reordered, &ours);
    assert_eq!(
        found.len(),
        2,
        "a swap disagrees at two positions: {found:?}"
    );
    assert!(found.iter().all(|f| f.contains("olean- and ABI-visible")));

    // 3. Upstream gained a constructor. Distinct from a rename: nothing disagrees
    //    positionally, so a position-only check would pass this.
    let mut gained = honest.clone();
    gained.push("quot".into());
    let found = divergences("Lean.Expr", "row", &gained, &ours);
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(
        found[0].contains("does not implement: quot"),
        "a gained constructor must be named: {found:?}"
    );

    // 4. Upstream dropped one we still implement — the opposite direction, and the one a
    //    "pin has everything we have" check would miss.
    let mut lost = honest;
    let dropped = lost.pop().expect("non-empty");
    assert_eq!(dropped, "proj");
    let found = divergences("Lean.Expr", "row", &lost, &ours);
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(
        found[0].contains("the pin does not declare: proj"),
        "an over-implemented constructor must be named: {found:?}"
    );
}

/// The parse must survive the binary's message decoration, must not invent rows, and must
/// keep an unanswerable type separate from an empty one.
#[test]
fn the_parse_is_anchored_on_markers_and_reports_what_it_could_not_read() {
    let noisy = "probe.lean:4:2: information: CTOR|Lean.Name|Lean.Name.anonymous\n\
                 some unrelated diagnostic text mentioning constructors\n\
                 CTOR|Lean.Name|Lean.Name.str\n\
                 MISSING|Lean.Nope\n\
                 NOTINDUCTIVE|Lean.Expr.app\n\
                 PROBE_COMPLETE\n";
    let parsed = parse_answer(noisy);
    assert!(parsed.complete);
    assert_eq!(
        parsed.ctors.get("Lean.Name").map(Vec::as_slice),
        Some(["anonymous".to_string(), "str".to_string()].as_slice()),
        "the type prefix must be stripped and order preserved: {:?}",
        parsed.ctors
    );
    assert_eq!(parsed.ctors.len(), 1, "no type may be invented from prose");
    assert_eq!(parsed.unanswerable.len(), 2);
    assert!(parsed.unanswerable[0].contains("declares no constant by that name"));
    assert!(parsed.unanswerable[1].contains("is not an inductive"));

    // A constructor that does not carry its type's prefix is kept whole, so it surfaces as a
    // divergence rather than being rewritten into agreement.
    let odd = parse_answer("CTOR|Lean.Name|Other.anonymous\n");
    assert_eq!(
        odd.ctors.get("Lean.Name").map(Vec::as_slice),
        Some(["Other.anonymous".to_string()].as_slice())
    );

    // Silence is not completion.
    let empty = parse_answer("nothing here\n");
    assert!(empty.ctors.is_empty() && empty.unanswerable.is_empty() && !empty.complete);
}

/// The probe must ask about exactly the types the comparison consumes. If these two lists
/// could drift, a type would drop out of the question while staying in the answer's expected
/// key set — the join this rig is built to close, applied to the rig itself.
#[test]
fn the_probe_asks_about_every_inventory_and_nothing_else() {
    let types: Vec<&str> = INVENTORIES.iter().map(|inv| inv.lean_type).collect();
    let source = probe_source(&types);
    for name in &types {
        assert!(
            source.contains(&format!("`{name}")),
            "{name} is compared but never asked about"
        );
    }
    assert!(
        !source.contains("@TARGETS@"),
        "the target list was not substituted, so the probe would ask about nothing"
    );
    for inv in &INVENTORIES {
        assert!(
            inv.ledger_row.ends_with(".ctorInventory"),
            "{} is not a ctorInventory row",
            inv.ledger_row
        );
    }
}

/// This rig's scope, against the ledger — checked in the only direction that stays true as
/// the remainder shrinks.
///
/// Deleting an entry from [`INVENTORIES`] narrows the probe and the comparison *together*,
/// so every other check here still passes while a published L2 row quietly loses the
/// evidence this rig exists to give it. That is AGENTS.md item 7's shape — a claim and its
/// evidence with an unwatched join — so the count is pinned.
///
/// The membership direction is deliberately one-way. Asserting that each backed row is
/// still IN `SOURCE_READ_ABOVE_L1_ALLOWANCE` would fail the moment `ci/PARITY_LEDGER.txt`
/// is repaired and the row leaves the remainder — turning a correct repair into someone
/// else's red build. A repaired row that this rig still corroborates is the intended end
/// state, not a defect.
#[test]
fn this_rig_backs_four_ledger_rows_and_every_unrepaired_ctor_row_is_among_them() {
    let mut backed: Vec<&str> = INVENTORIES.iter().map(|inv| inv.ledger_row).collect();
    backed.sort_unstable();
    backed.dedup();
    assert_eq!(
        backed.len(),
        4,
        "this rig backs {} distinct ledger row(s), not the 4 ctorInventory rows of bead \
         fln-parity-ledger-l2-pinned-source-qydn: {backed:?}. An inventory was added or \
         removed, and a removed one takes a published row's evidence with it",
        backed.len()
    );

    for symbol in fln_conformance::ledger::SOURCE_READ_ABOVE_L1_ALLOWANCE {
        if !symbol.ends_with(".ctorInventory") {
            continue;
        }
        assert!(
            backed.contains(&symbol),
            "`{symbol}` is still in the declared remainder as a source-read L2 row, and no \
             inventory here backs it — the remainder names a row this rig was supposed to \
             give a value-producing oracle"
        );
    }
}
