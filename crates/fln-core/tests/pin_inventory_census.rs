//! Mechanical census of the term-plane inventory against the PINNED Reference
//! sources (bead franken_lean-p8a; doctrine D5/D9).
//!
//! fln-core is the vocabulary every other crate compiles against, so "complete
//! against the pin" has to be a checked fact rather than a claim someone made once
//! while reading upstream. D5/D9 forbids hand-transcribed inventories and layout
//! constants for exactly the reason this file exists: a transcription is correct on
//! the day it is written and silently wrong after the next epoch bump.
//!
//! So nothing here is written down twice. The census reads
//! `vendor/lean4-src/src/**` — the pin's own sources, vendored and tracked, in their
//! D8 role as census mine, never as a runtime component — extracts the constructor
//! lists and option defaults, and compares them to what this crate implements. If
//! upstream gains a constructor, renames one, or changes a default, this test fails
//! and names the difference.
//!
//! It reads files at test time rather than `include_str!`-ing them so that a missing
//! vendor tree degrades to a typed skip instead of a build error; the vendored
//! sources are tracked, so a skip in CI means the checkout is wrong, and it says so.
//!
//! Nothing in this file adds a dependency: fln-core is rank 0 in
//! ci/WORKSPACE_GRAPH.txt with zero dependencies and must stay that way. This is
//! std-only string scanning over text files.

#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};

use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level, LevelView};
use fln_core::name::{LeafView, Name};
use fln_core::options::{DataValue, KVMap, limits};

fn pin_root() -> Option<PathBuf> {
    let root = fln_core::checked_workspace_root!().join("vendor/lean4-src/src");
    root.is_dir().then_some(root)
}

fn read(root: &Path, rel: &str) -> String {
    let path = root.join(rel);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("cannot read pinned source {}: {error}", path.display()))
}

/// Constructor names of an `inductive` block, in declaration order.
///
/// The block ends at the first line that starts a new top-level item (column 0, not
/// a comment and not a continuation), which is how these files are laid out. A shape
/// this cannot parse is a failure, never an empty list quietly reported as agreement.
fn inductive_constructors(source: &str, name: &str) -> Vec<String> {
    let header = format!("inductive {name}");
    let start = source
        .lines()
        .position(|line| line.trim_end() == header || line.starts_with(&format!("{header} ")))
        .unwrap_or_else(|| panic!("no `inductive {name}` in the pinned source"));

    let mut constructors = Vec::new();
    for line in source.lines().skip(start + 1) {
        let trimmed = line.trim_start();
        if trimmed.starts_with("|") {
            let rest = trimmed.trim_start_matches('|').trim_start();
            let ctor: String = rest
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_' || *c == '\'')
                .collect();
            if !ctor.is_empty() {
                constructors.push(ctor);
            }
            continue;
        }
        // Still inside the block: indented continuations, blank lines, doc comments.
        if line.is_empty()
            || line.starts_with(' ')
            || line.starts_with("--")
            || line.starts_with("/-")
            || line.starts_with("deriving")
        {
            continue;
        }
        break;
    }
    assert!(
        !constructors.is_empty(),
        "parsed no constructors for `{name}` — the pin's layout changed and this \
         census parser must be updated rather than left silently agreeing"
    );
    constructors
}

/// `register_builtin_option <name> : … defValue := <n>`.
fn option_default(source: &str, option: &str) -> u64 {
    for marker in ["register_builtin_option ", "register_option "] {
        let needle = format!("{marker}{option} ");
        let Some(at) = source.find(&needle) else {
            continue;
        };
        let block = &source[at..(at + 600).min(source.len())];
        let value_at = block
            .find("defValue")
            .unwrap_or_else(|| panic!("`{option}` has no defValue within its registration block"));
        let digits: String = block[value_at..]
            .chars()
            .skip_while(|c| !c.is_ascii_digit())
            .take_while(char::is_ascii_digit)
            .collect();
        return digits
            .parse()
            .unwrap_or_else(|_| panic!("`{option}` defValue is not a plain literal"));
    }
    panic!("no registration for option `{option}` in the pinned source");
}

/// The census is the point of the test, so a missing pin is reported and skipped
/// rather than passing quietly.
macro_rules! pin_or_skip {
    () => {
        match pin_root() {
            Some(root) => root,
            None => {
                eprintln!(
                    "SKIP: vendor/lean4-src is absent. It is tracked in git, so this means the \
                     checkout is incomplete — the census did NOT run and proves nothing."
                );
                return;
            }
        }
    };
}

/// Every constructor upstream declares, this crate implements — and nothing extra.
///
/// The Rust side is enumerated by *constructing* a value per arm and matching on it,
/// so adding a variant to any of these enums without adding it here fails to compile
/// on the match, and adding one upstream fails the comparison below.
#[test]
fn the_constructor_inventory_matches_the_pin() {
    let root = pin_or_skip!();

    let prelude = read(&root, "Init/Prelude.lean");
    let level_src = read(&root, "Lean/Level.lean");
    let expr_src = read(&root, "Lean/Expr.lean");
    let kvmap_src = read(&root, "Lean/Data/KVMap.lean");

    // ---- Name -----------------------------------------------------------------
    let ours: Vec<&str> = [
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
    .collect();
    assert_eq!(
        inductive_constructors(&prelude, "Name"),
        ours,
        "Name inventory diverged from the pin"
    );

    // ---- Level ----------------------------------------------------------------
    let param = Name::str(Name::anonymous(), "u");
    let levels = [
        Level::zero(),
        Level::zero().succ().expect("shallow"),
        Level::max(Level::zero(), Level::zero()).expect("shallow"),
        Level::imax(Level::zero(), Level::zero()).expect("shallow"),
        Level::param(param.clone()),
        Level::mvar(LMVarId(param.clone())),
    ];
    let ours: Vec<&str> = levels
        .iter()
        .map(|level| match level.view() {
            LevelView::Zero => "zero",
            LevelView::Succ(_) => "succ",
            LevelView::Max(..) => "max",
            LevelView::IMax(..) => "imax",
            LevelView::Param(_) => "param",
            LevelView::MVar(_) => "mvar",
        })
        .collect();
    assert_eq!(
        inductive_constructors(&level_src, "Level"),
        ours,
        "Level inventory diverged from the pin"
    );

    // ---- Expr -----------------------------------------------------------------
    let leaf = Expr::bvar(0).expect("small");
    let exprs = [
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
        Expr::proj(param.clone(), 0, leaf.clone()),
    ];
    let ours: Vec<&str> = exprs
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
        .collect();
    assert_eq!(
        inductive_constructors(&expr_src, "Expr"),
        ours,
        "Expr inventory diverged from the pin"
    );

    // ---- Literal --------------------------------------------------------------
    let ours: Vec<&str> = [
        Literal::Nat(NatLit::from_u64(0)),
        Literal::Str(String::new()),
    ]
    .iter()
    .map(|literal| match literal {
        Literal::Nat(_) => "natVal",
        Literal::Str(_) => "strVal",
    })
    .collect();
    assert_eq!(
        inductive_constructors(&expr_src, "Literal"),
        ours,
        "Literal inventory diverged from the pin"
    );

    // ---- BinderInfo -----------------------------------------------------------
    let ours: Vec<&str> = [
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
    .collect();
    assert_eq!(
        inductive_constructors(&expr_src, "BinderInfo"),
        ours,
        "BinderInfo inventory diverged from the pin"
    );

    // ---- DataValue ------------------------------------------------------------
    let ours: Vec<&str> = [
        DataValue::OfString(String::new()),
        DataValue::OfBool(false),
        DataValue::OfName(param.clone()),
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
    .collect();
    assert_eq!(
        inductive_constructors(&kvmap_src, "DataValue"),
        ours,
        "DataValue inventory diverged from the pin"
    );
}

/// The resource limits carried by [`limits`] are the pin's registered defaults, and
/// this reads them out of the pin rather than trusting the transcription (D5/D9).
///
/// These are not decoration: `maxHeartbeats` and `maxRecDepth` bound elaboration and
/// recursion, and a wrong default silently changes where the toolchain gives up.
#[test]
fn the_resource_limits_match_the_pin() {
    let root = pin_or_skip!();

    let core_m = read(&root, "Lean/CoreM.lean");
    assert_eq!(
        option_default(&core_m, "maxHeartbeats"),
        limits::MAX_HEARTBEATS_DEFAULT
    );

    let synth = read(&root, "Lean/Meta/SynthInstance.lean");
    assert_eq!(
        option_default(&synth, "synthInstance.maxHeartbeats"),
        limits::SYNTH_INSTANCE_MAX_HEARTBEATS_DEFAULT
    );
    assert_eq!(
        option_default(&synth, "synthInstance.maxSize"),
        limits::SYNTH_INSTANCE_MAX_SIZE_DEFAULT
    );

    let meta = read(&root, "Lean/Meta/Basic.lean");
    assert_eq!(
        option_default(&meta, "maxSynthPendingDepth"),
        limits::MAX_SYNTH_PENDING_DEPTH_DEFAULT
    );

    let elab_level = read(&root, "Lean/Elab/Level.lean");
    assert_eq!(
        option_default(&elab_level, "maxUniverseOffset"),
        limits::MAX_UNIVERSE_OFFSET_DEFAULT
    );

    let safe_exp = read(&root, "Lean/Util/SafeExponentiation.lean");
    assert_eq!(
        option_default(&safe_exp, "exponentiation.threshold"),
        limits::EXPONENTIATION_THRESHOLD_DEFAULT
    );

    let language = read(&root, "Lean/Language/Basic.lean");
    assert_eq!(
        option_default(&language, "maxErrors"),
        limits::MAX_ERRORS_DEFAULT
    );

    // `defaultMaxRecDepth` is a plain definition, not a registered option.
    let prelude = read(&root, "Init/Prelude.lean");
    let at = prelude
        .find("def defaultMaxRecDepth")
        .expect("defaultMaxRecDepth is defined in the prelude");
    let digits: String = prelude[at..]
        .chars()
        .skip_while(|c| !c.is_ascii_digit())
        .take_while(char::is_ascii_digit)
        .collect();
    assert_eq!(
        digits.parse::<u64>().expect("a plain literal"),
        limits::MAX_REC_DEPTH_DEFAULT
    );
}
