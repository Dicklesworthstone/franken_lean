//! Unit, pin-gated E2E, and negative-control tests for the K1 vs Reference
//! kernel unfold-count differential (bead `fln-kernel-unfold-differential-tfvw`).

#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::path::PathBuf;

use fln_conformance::unfold_differential::{
    LoadedOleanModule, display_counts, join_and_rank, parse_pin_unfold_output,
    run_pin_unfold_counts,
};
use fln_core::expr::{BinderInfo, Expr};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_env::constants::{
    AxiomVal, ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
    TheoremVal,
};
use fln_env::environment::{Environment, ProvisionalEnvironment};
use fln_kernel::verdict::Budget;
use fln_kernel::{Declaration, observe_unfolds};

const PIN_TAG: &str = "leanprover--lean4---v4.32.0";
const STACK_BYTES: usize = 32 * 1024 * 1024;

fn pinned_toolchain() -> Option<(PathBuf, PathBuf)> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home)
                    .join(".elan/toolchains")
                    .join(PIN_TAG)
                    .join("lib/lean")
            })
        })
        .filter(|p| p.join("Init/Prelude.olean").is_file());
    let bin = lib
        .as_ref()
        .and_then(|p| p.parent())
        .and_then(|p| p.parent())
        .map(|root| root.join("bin/lean"))
        .filter(|p| p.is_file());
    let pair = bin.zip(lib);
    assert!(
        pair.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "FLN_REQUIRE_REFERENCE is set and pinned Reference {PIN_TAG} is absent"
    );
    if pair.is_none() {
        eprintln!("SKIP: pinned Reference {PIN_TAG} absent");
    }
    pair
}

fn binary_digest_hex(path: &std::path::Path) -> String {
    let bytes = std::fs::read(path).expect("read binary for digest");
    fln_hash::domain::hash(fln_hash::domain::Domain::OperationalMeta, &bytes).to_hex()
}

#[test]
fn join_and_rank_orders_by_ratio_and_separates_one_sided_and_zero_counts() {
    let k1 = BTreeMap::from([
        ("Alpha".to_owned(), 100),
        ("Beta".to_owned(), 20),
        ("Gamma".to_owned(), 20),
        ("OnlyK1Big".to_owned(), 999),
        ("OnlyK1Small".to_owned(), 3),
        ("ZeroOnK1".to_owned(), 0),
        ("ZeroBoth".to_owned(), 0),
    ]);
    let pin = BTreeMap::from([
        ("Alpha".to_owned(), 50), // 2.0x
        ("Beta".to_owned(), 2),   // 10.0x
        ("Gamma".to_owned(), 2),  // 10.0x (tie -> alphabetical)
        ("OnlyPinBig".to_owned(), 77),
        ("OnlyPinSmall".to_owned(), 1),
        ("ZeroOnK1".to_owned(), 5), // treated as pin_only
        ("ZeroOnPin".to_owned(), 0),
        ("ZeroBoth".to_owned(), 0),
    ]);

    let report = join_and_rank(&k1, &pin);
    assert_eq!(report.total_k1_unfolds, 1142);
    assert_eq!(report.total_pin_unfolds, 137);
    assert!((report.max_shared_ratio - 10.0).abs() < 1e-9);

    let shared_names: Vec<&str> = report
        .shared_ranked
        .iter()
        .map(|r| r.name.as_str())
        .collect();
    assert_eq!(shared_names, vec!["Beta", "Gamma", "Alpha"]);
    assert!((report.shared_ranked[0].ratio - 10.0).abs() < 1e-9);
    assert!((report.shared_ranked[2].ratio - 2.0).abs() < 1e-9);

    assert_eq!(
        report.k1_only,
        vec![("OnlyK1Big".to_owned(), 999), ("OnlyK1Small".to_owned(), 3)]
    );
    assert_eq!(
        report.pin_only,
        vec![
            ("OnlyPinBig".to_owned(), 77),
            ("ZeroOnK1".to_owned(), 5),
            ("OnlyPinSmall".to_owned(), 1),
        ]
    );
}

#[test]
fn parse_pin_unfold_output_validates_headers_sorting_and_entry_count() {
    let valid = "\
# module\tInit.Prelude
# declaration\tList.append
# verdict\taccepted
# wall_ns\t123456
# entries\t2
List.rec\t14
Nat.rec\t7
";
    let parsed = parse_pin_unfold_output(valid).expect("valid output parses");
    assert_eq!(parsed.module, "Init.Prelude");
    assert_eq!(parsed.declaration, "List.append");
    assert_eq!(parsed.wall_ns, 123456);
    assert_eq!(parsed.counts.get("List.rec"), Some(&14));
    assert_eq!(parsed.counts.get("Nat.rec"), Some(&7));

    let unsorted = "\
# module\tInit.Prelude
# declaration\tList.append
# verdict\taccepted
# wall_ns\t1
# entries\t2
Nat.rec\t7
List.rec\t14
";
    assert!(parse_pin_unfold_output(unsorted).is_err());
}

/// Negative control: deliberately forcing left-first lazy delta unfolding in K1
/// breaks hint-height alignment on a constructed tower of definitions and drives
/// an unfold ratio strictly past the control bound, proving the instrument detects
/// real lazy-delta priority divergences.
#[test]
fn negative_control_forced_left_delta_moves_unfold_ratio_past_bound() {
    let n = |s: &str| Name::from_components(s.split('.'));
    let prop = Expr::sort(Level::zero());
    let type0 = Expr::sort(Level::succ(Level::zero()).expect("succ level"));
    let c = |s: &str| Expr::const_(n(s), Vec::new());
    let bv = |i: u32| Expr::bvar(i).expect("bvar");

    // Axiom P : Type, a : P, Eq : (α : Type) → α → α → Prop, refl : (α : Type) → (x : α) → Eq α x x
    let mut env = ProvisionalEnvironment::from_admitted(Environment::new());
    let eq_ty = Expr::forall_e(
        n("α"),
        type0.clone(),
        Expr::forall_e(
            n("x"),
            bv(0),
            Expr::forall_e(n("y"), bv(1), prop.clone(), BinderInfo::Default),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let refl_ty = Expr::forall_e(
        n("α"),
        type0.clone(),
        Expr::forall_e(
            n("x"),
            bv(0),
            Expr::app(Expr::app(Expr::app(c("Eq"), bv(1)), bv(0)), bv(0)),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );

    // Build a deep chain: d0 = a (height 1), d1 = d0 (height 2), ..., d12 = d11 (height 13),
    // and wrap_left = d12 (height 14), wrap_right = d12 (height 14),
    // plus an outer alias `hi` (height 15) = d12 vs `lo` (height 14) = d12.
    // Even sharper: `low` (height 1) := `a` wrapped through 10 nested defs `h1..h10`,
    // and compare `h10 =?= h10_alias` where `h10_alias` (height 12) := `h10` (height 11):
    // - Priority-correct K1 unfolds `h10_alias` ONCE (height 12 > 11) -> `h10 =?= h10` -> instant structural hit! (0 unfolds of h1..h10!)
    // - Forced left-first K1 unfolds `h10` -> `h9` -> ... -> `h1` -> `a` BEFORE touching `h10_alias` (11 extra unfolds of h10..h1)!
    let mut constants = vec![
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("P"),
                level_params: Vec::new(),
                type_: type0.clone(),
            },
            is_unsafe: false,
        }),
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("a"),
                level_params: Vec::new(),
                type_: c("P"),
            },
            is_unsafe: false,
        }),
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("Eq"),
                level_params: Vec::new(),
                type_: eq_ty,
            },
            is_unsafe: false,
        }),
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("refl"),
                level_params: Vec::new(),
                type_: refl_ty,
            },
            is_unsafe: false,
        }),
    ];
    let mut prev = c("a");
    for i in 1..=10_u32 {
        let name = format!("h{i}");
        constants.push(ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: n(&name),
                level_params: Vec::new(),
                type_: c("P"),
            },
            value: prev,
            hints: ReducibilityHints::Regular(i),
            safety: DefinitionSafety::Safe,
            all: vec![n(&name)],
        }));
        prev = c(&name);
    }
    constants.push(ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: n("h10_alias"),
            level_params: Vec::new(),
            type_: c("P"),
        },
        value: c("h10"),
        hints: ReducibilityHints::Regular(11),
        safety: DefinitionSafety::Safe,
        all: vec![n("h10_alias")],
    }));
    env = env
        .assume_constants(&constants)
        .expect("populate fixture env");

    // theorem check_eq : Eq P h10 h10_alias := refl P h10
    // Checking `Eq P h10 h10 =?= Eq P h10 h10_alias` compares `t = h10` (height 10) vs `s = h10_alias` (height 11).
    let thm = Declaration::Thm(TheoremVal {
        base: ConstantVal {
            name: n("check_eq"),
            level_params: Vec::new(),
            type_: Expr::app(
                Expr::app(Expr::app(c("Eq"), c("P")), c("h10")),
                c("h10_alias"),
            ),
        },
        value: Expr::app(Expr::app(c("refl"), c("P")), c("h10")),
        all: vec![n("check_eq")],
    });

    let budget = Budget::for_stack_bytes(STACK_BYTES);
    let good = observe_unfolds(env.as_check_environment(), &thm, budget, false);
    let bad = observe_unfolds(env.as_check_environment(), &thm, budget, true);

    let good_counts = display_counts(&good.unfolds);
    let bad_counts = display_counts(&bad.unfolds);
    let diff = join_and_rank(&bad_counts, &good_counts);

    assert_eq!(
        good_counts.get("h10_alias").copied().unwrap_or(0),
        1,
        "priority-correct K1 should unfold only h10_alias once: {good_counts:?}"
    );
    assert_eq!(
        good_counts.get("h10").copied().unwrap_or(0),
        0,
        "priority-correct K1 must not unfold h10: {good_counts:?}"
    );
    assert!(
        diff.k1_only.len() >= 10,
        "forced left-delta negative control must unfold h10..h1 unnecessarily: {}",
        diff.render_top(15)
    );
}

/// Pin-gated E2E control: runs both `scripts/tribunal/unfold_counts.lean` (stock
/// pinned Lean v4.32.0) and `fln_kernel::observe_unfolds` (K1) on ten Prelude
/// declarations, verifying non-empty sorted tables and a tight control ratio bound.
#[test]
fn pin_gated_e2e_prelude_control_unfold_counts_agree_within_bound() {
    let Some((pin_lean, pin_lib)) = pinned_toolchain() else {
        return;
    };
    let root = fln_conformance::checked_workspace_root!();
    let pin_digest = binary_digest_hex(&pin_lean);
    let lean_path = pin_lib.to_string_lossy().to_string();
    let roots = vec![pin_lib.clone()];
    let budget = Budget::for_stack_bytes(STACK_BYTES);

    // Ten real Init.Prelude declarations that exercise non-trivial kernel unfolding/iota.
    let controls = [
        "Lean.ParserDescr.noConfusion",
        "Lean.ParserDescr.noConfusionType",
        "Lean.ParserDescr.ctorElim",
        "Lean.ParserDescr.brecOn.go",
        "Lean.ParserDescr.ctorIdx",
        "Lean.Syntax.noConfusion",
        "Lean.Syntax.ctorElim",
        "Lean.Syntax.brecOn.go",
        "Lean.Name.noConfusion",
        "Lean.Name.ctorElim",
    ];

    eprintln!(
        "unfold_differential E2E: pin_lean={} blake3={pin_digest}",
        pin_lean.display()
    );
    let loaded =
        LoadedOleanModule::load(&roots, "Init.Prelude").expect("load Init.Prelude closure once");
    let mut non_empty_checked = 0_usize;
    let control_ratio_bound = 2.0_f64;

    for decl in controls {
        let module = "Init.Prelude";
        let pin_table = run_pin_unfold_counts(&root, &pin_lean, &lean_path, module, decl)
            .unwrap_or_else(|e| panic!("pin failed on {module}::{decl}: {e}"));
        let k1_run = loaded
            .observe_declaration(decl, budget, false)
            .unwrap_or_else(|e| panic!("K1 failed on {module}::{decl}: {e}"));
        assert_eq!(
            k1_run.verdict_label(),
            "accepted",
            "K1 must accept control {module}::{decl}"
        );
        let k1_counts = k1_run.display_counts();
        let report = join_and_rank(&k1_counts, &pin_table.counts);
        eprintln!(
            "CONTROL {module}::{decl} | pin_rows={} k1_rows={} pin_ms={:.2} k1_ms={:.2} k1_steps={} max_ratio={:.3}\n{}",
            pin_table.counts.len(),
            k1_counts.len(),
            (pin_table.wall_ns as f64) / 1e6,
            k1_run.wall.as_secs_f64() * 1e3,
            k1_run.observation.steps_used,
            report.max_shared_ratio,
            report.render_top(5),
        );
        if !pin_table.counts.is_empty() {
            non_empty_checked += 1;
            assert!(
                !k1_counts.is_empty(),
                "K1 unfold table was empty where pin had {} rows for {module}::{decl}",
                pin_table.counts.len()
            );
            assert!(
                report.max_shared_ratio <= control_ratio_bound,
                "control {module}::{decl} exceeded ratio bound {control_ratio_bound}x:\n{}",
                report.render_top(10)
            );
        }
    }
    assert_eq!(
        non_empty_checked,
        controls.len(),
        "expected all 10 Prelude control tables to be non-empty, got {non_empty_checked}"
    );
}
