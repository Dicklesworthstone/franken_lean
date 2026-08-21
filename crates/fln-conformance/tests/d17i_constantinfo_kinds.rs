//! `franken_lean-d17i`: the exported/private ConstantInfo-kind split, by name.
//!
//! d17i spent four passes deciding whether its 13 `DefinitionTypeMismatch` rows
//! were genuine defeq incompleteness or a measurement artifact. It settled on
//! artifact after looking five definitions up and finding every one of them
//! decoded as an `Axiom` with no value. The repair (`37ee8d81` / `1391adcf`)
//! then loaded the module-system companion chain — but nothing ever re-checked
//! those five BY NAME, so the bead's central claim rested on an aggregate
//! measurement taken before the fix and never repeated after it.
//!
//! This pins it at both ends. For each declaration the bead names, the exported
//! part must still read `Axiom` and the private part must read `Defn`. The
//! exported half is not decoration: it is what stops the suite passing if
//! someone points both reads at the private part, and it is the observation
//! d17i actually recorded on 2026-07-25.
//!
//! ONE THING THIS FILE CORRECTS. d17i describes the exported reading as our
//! decoder "stripping" values. It is not. Lean's module system writes
//! non-exposed bodies to `.olean.private` and stores the postulated type in the
//! exported part deliberately, so the exported `axiomInfo` is genuinely on
//! disk and our decoder was faithful to it. The defect was which PART the
//! decoder was pointed at. Anyone hunting a value-stripping bug inside
//! `decode_constant_info` will find nothing there, which is why the exported
//! expectation below is spelled `Axiom` rather than "wrong".
//!
//! Scope: these are the modules d17i names, not the corpus. Zero declarations
//! lost between the two parts is measured here over those modules only;
//! `fln-olean`'s own companion suite carries the wider statement.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use fln_core::expr::{BinderInfo, Expr, ExprNode};
use fln_core::level::LevelView;
use fln_core::name::Name;
use fln_env::constants::{
    ConstantInfo, ConstantVal, ConstructorVal, DefinitionSafety, InductiveVal, QuotKind,
    RecursorVal, ReducibilityHints,
};
use fln_olean::decl::DeclDecoder;
use fln_olean::region::{ModuleDataView, OleanView, WalkBudget};

/// Pin discovery: `FLN_REFERENCE_LIB` when set, otherwise the elan-installed
/// toolchain. Absent pin is a loud skip rather than a silent pass — a remote
/// worker has no `~/.elan`, and a quiet green there would be indistinguishable
/// from a real one.
fn reference_lib() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("FLN_REFERENCE_LIB") {
        let path = PathBuf::from(path);
        return path.is_dir().then_some(path);
    }
    let home = std::env::var("HOME").ok()?;
    let path = PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean");
    path.is_dir().then_some(path)
}

macro_rules! lib_or_skip {
    () => {
        match reference_lib() {
            Some(lib) => lib,
            None => {
                eprintln!(
                    "SKIP: pinned Reference stdlib not installed; this lane measures real \
                     module-system olean parts and has no fixture substitute"
                );
                return;
            }
        }
    };
}

fn kind_of(info: &ConstantInfo) -> &'static str {
    match info {
        ConstantInfo::Axiom(_) => "Axiom",
        ConstantInfo::Defn(_) => "Defn",
        ConstantInfo::Thm(_) => "Thm",
        ConstantInfo::Opaque(_) => "Opaque",
        ConstantInfo::Quot(_) => "Quot",
        ConstantInfo::Induct(_) => "Induct",
        ConstantInfo::Ctor(_) => "Ctor",
        ConstantInfo::Rec(_) => "Rec",
    }
}

fn kinds(infos: &[ConstantInfo]) -> BTreeMap<String, &'static str> {
    infos
        .iter()
        .map(|info| (info.name().to_display_string(), kind_of(info)))
        .collect()
}

/// Decode one module twice: from the exported part alone, and from the
/// private part with its two earlier regions supplied as dependencies — the
/// same two readings d17i's before and after correspond to.
fn exported_and_private(
    lib: &Path,
    module: &str,
) -> (
    BTreeMap<String, &'static str>,
    BTreeMap<String, &'static str>,
) {
    let base = lib.join(format!("{module}.olean"));
    let read = |path: &Path| std::fs::read(path).unwrap_or_else(|e| panic!("read {path:?}: {e}"));
    let exported = read(&base);
    let server = read(&base.with_extension("olean.server"));
    let private = read(&base.with_extension("olean.private"));

    let exported_view = OleanView::parse(&exported).expect("parse exported part");
    let exported_infos = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .expect("decode exported part");

    let private_view = OleanView::parse_with_dependencies(&private, &[&exported, &server])
        .expect("parse private part against its earlier regions");
    let private_infos = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("decode private part");

    (kinds(&exported_infos), kinds(&private_infos))
}

/// The five definitions d17i could not classify, with the module each lives in.
const FIVE: &[(&str, &str)] = &[
    ("Lean.Arrow", "Init/SimpLemmas"),
    ("Option.choice", "Init/Data/Option/Lemmas"),
    ("WellFounded.fixFC", "Init/WFComputable"),
    ("Array.insertIdxIfInBounds", "Init/Data/Array/Basic"),
    (
        "Std.PRange.UpwardEnumerable.least",
        "Init/Data/Range/Polymorphic/UpwardEnumerable",
    ),
];

#[test]
fn the_five_unclassified_definitions_are_axioms_exported_and_definitions_private() {
    let lib = lib_or_skip!();
    for (declaration, module) in FIVE {
        let (exported, private) = exported_and_private(&lib, module);
        assert_eq!(
            exported.get(*declaration).copied(),
            Some("Axiom"),
            "{declaration}: the exported part is supposed to carry a postulated type. If this \
             ever changes, the `Defn` below stops being evidence of anything — both reads could \
             be hitting the same part."
        );
        assert_eq!(
            private.get(*declaration).copied(),
            Some("Defn"),
            "{declaration}: the private part must restore the body. A regression here puts \
             d17i's five rows back to unclassified."
        );
    }
}

/// The auxiliary family behind the 24 `UnknownConstant` rows and the 8
/// `DefinitionTypeMismatch` rows that shared their root cause.
const AUXILIARIES: &[(&str, &str, &str)] = &[
    (
        "_private.Init.Data.List.ToArrayImpl.0.List.toArrayAux.match_1",
        "Init/Data/List/ToArrayImpl",
        "Defn",
    ),
    (
        "_private.Init.Prelude.0.Lean.Name.beq.match_1",
        "Init/Prelude",
        "Defn",
    ),
    (
        "_private.Init.Prelude.0.Lean.Name.hash._proof_1",
        "Init/Prelude",
        "Thm",
    ),
    (
        "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1",
        "Init/Prelude",
        "Defn",
    ),
    (
        "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop.match_1",
        "Init/Prelude",
        "Defn",
    ),
];

#[test]
fn the_named_private_auxiliaries_are_exported_absent_and_private_present() {
    let lib = lib_or_skip!();
    for (declaration, module, expected) in AUXILIARIES {
        let (exported, private) = exported_and_private(&lib, module);
        assert_eq!(
            exported.get(*declaration).copied(),
            None,
            "{declaration}: absence from the exported part is the precondition that made this an \
             UnknownConstant row in the first place"
        );
        assert_eq!(
            private.get(*declaration).copied(),
            Some(*expected),
            "{declaration}: the private part must supply the auxiliary the kernel was asked for"
        );
    }

    // The row that opened this bead. The equation lemma itself was never
    // missing — it is present in BOTH parts — so the rejection was caused by
    // `Lean.Arrow` being an axiom on the unfolding path defeq needed, not by
    // anything about the lemma. Asserting both halves keeps that distinction
    // from being re-litigated.
    let (exported, private) = exported_and_private(&lib, "Init/SimpLemmas");
    let eq_1 = "_private.Init.SimpLemmas.0.Lean.Arrow.eq_1";
    assert_eq!(exported.get(eq_1).copied(), Some("Thm"));
    assert_eq!(private.get(eq_1).copied(), Some("Thm"));
}

#[test]
fn kinds_are_discriminated_and_the_exported_name_set_is_never_lost() {
    let lib = lib_or_skip!();

    // A reader that answered `Defn` for everything would satisfy both tests
    // above. These four say it does not: genuine axioms stay axioms across the
    // same two reads that turn the five into definitions, and the structural
    // kinds survive intact.
    let (exported, private) = exported_and_private(&lib, "Init/Prelude");
    for (declaration, expected) in [
        ("Classical.choice", "Axiom"),
        ("sorryAx", "Axiom"),
        ("Nat", "Induct"),
        ("Nat.succ", "Ctor"),
    ] {
        assert_eq!(exported.get(declaration).copied(), Some(expected));
        assert_eq!(
            private.get(declaration).copied(),
            Some(expected),
            "{declaration}: the private read must not rewrite kinds wholesale"
        );
    }

    // Containment. The private part is used as the authoritative constant
    // array, so it has to be a superset — otherwise the repair trades the old
    // omission for a new one, and every decoded COUNT still rises, which means
    // the observable that caught the first defect cannot catch the second.
    for (_, module) in FIVE
        .iter()
        .chain(std::iter::once(&("", "Init/Data/List/ToArrayImpl")))
    {
        let (exported, private) = exported_and_private(&lib, module);
        let lost: Vec<&String> = exported
            .keys()
            .filter(|k| !private.contains_key(*k))
            .collect();
        assert!(
            lost.is_empty(),
            "{module}: the private part dropped names the exported part had: {lost:?}"
        );
        assert!(
            private.len() > exported.len(),
            "{module}: the private part is supposed to ADD declarations \
             (exported {}, private {})",
            exported.len(),
            private.len()
        );
    }

    // A census pinned independently by `kernel_replay`'s
    // `module_system_private_part_restores_bodies_and_private_auxiliaries`.
    // Two readers agreeing on the same two integers is what caught a name-
    // rendering bug in the throwaway probe this file replaces.
    let (exported, private) = exported_and_private(&lib, "Init/Data/List/ToArrayImpl");
    assert_eq!(exported.len(), 5, "pin's exported ToArrayImpl census");
    assert_eq!(private.len(), 6, "pin's private ToArrayImpl census");
}

/// Every declaration that is still `Axiom` after the private part is read, for
/// the two modules that hold all of them at the pin.
///
/// d17i measured that roughly 7,007 of 15,881 compared declarations — about 44
/// in 100 — were compared as axioms whose bodies our decoder had not supplied,
/// and warned that "we agreed with leanchecker" meant agreement on a postulated
/// type rather than a checked body for that fraction. This is the assertion
/// that keeps the answer honest once the companion chain restores them.
///
/// The residual set is pinned by NAME rather than by count. A count would be
/// satisfied by any fifteen survivors, and the whole question here is WHICH
/// declarations the kernel is still taking on trust: `propext`,
/// `Classical.choice`, `Quot.sound` and `sorryAx` are Lean's genuine axioms,
/// and the rest are compiler primitives (`lc*`, `isScalarObj`, `Quot.lcInv`,
/// `Lean.trustCompiler`, `Lean.ofReduceBool`, `Lean.ofReduceNat`). Every one is
/// declared `axiom` in the vendored pin source, so a postulate is the correct
/// reading for all of them. A sixteenth name appearing here is a real
/// definition whose body went missing again, and that is a finding, not noise.
const RESIDUAL_AXIOMS: &[(&str, &[&str])] = &[
    (
        "Init/Prelude",
        &[
            "Classical.choice",
            "Quot.lcInv",
            "isScalarObj",
            "lcAny",
            "lcCast",
            "lcErased",
            "lcProof",
            "lcUnreachable",
            "lcVoid",
            "sorryAx",
        ],
    ),
    (
        "Init/Core",
        &[
            "Lean.ofReduceBool",
            "Lean.ofReduceNat",
            "Lean.trustCompiler",
            "Quot.sound",
            "propext",
        ],
    ),
];

#[test]
fn the_only_declarations_still_postulated_are_the_pins_real_axioms() {
    let lib = lib_or_skip!();
    for (module, expected) in RESIDUAL_AXIOMS {
        let (exported, private) = exported_and_private(&lib, module);
        let residual: Vec<&str> = exported
            .iter()
            .filter(|(name, kind)| {
                **kind == "Axiom" && private.get(*name).copied() == Some("Axiom")
            })
            .map(|(name, _)| name.as_str())
            .collect();
        assert_eq!(
            residual, *expected,
            "{module}: the set of declarations the kernel still takes on trust has moved. \
             A NEW name here is a definition whose body stopped being supplied — d17i's \
             stripped-axiom defect returning — and a MISSING name means one of the pin's \
             own axioms stopped being decoded."
        );
        // Anti-vacuity: the exported part must carry far more axioms than
        // survive, or this test would pass against a decoder that had never
        // stripped anything and would prove nothing about the repair.
        let exported_axioms = exported.values().filter(|kind| **kind == "Axiom").count();
        assert!(
            exported_axioms > expected.len() * 10,
            "{module}: expected the exported part to postulate far more than the {} that \
             survive, got {exported_axioms}",
            expected.len()
        );
    }
}

/// One bounded step beyond `Init`, chosen because this bead already names a
/// declaration inside it.
///
/// d17i's exhaustive pass listed four definitions that appeared in BOTH the
/// UnknownConstant and the DefinitionTypeMismatch families, and
/// `Std.DHashMap.Internal.AssocList.contains` was one of them. Init is the
/// module set every earlier increment measured; carrying the same two-part
/// reading into a named `Std` prefix is what shows the companion repair is a
/// property of the module system rather than of `Init`.
const STD_PREFIX: &str = "Std/Data/DHashMap";
/// A declaration this bead names, and the module that holds it at the pin.
const STD_NAMED_ROW: (&str, &str) = (
    "Std.DHashMap.Internal.AssocList.contains",
    "Std/Data/DHashMap/Internal/AssocList/Basic",
);

/// Every module under `root` that carries a complete three-part chain, as
/// library-relative module paths.
fn complete_chains_under(lib: &Path, root: &Path) -> Vec<String> {
    let mut out = Vec::new();
    let mut directories = vec![root.to_path_buf()];
    while let Some(directory) = directories.pop() {
        let entries = match std::fs::read_dir(&directory) {
            Ok(entries) => entries,
            Err(error) => panic!("read {}: {error}", directory.display()),
        };
        for entry in entries {
            let path = entry.expect("library entry").path();
            if path.is_dir() {
                directories.push(path);
                continue;
            }
            if path.extension().is_some_and(|e| e == "olean")
                && path.with_extension("olean.server").exists()
                && path.with_extension("olean.private").exists()
            {
                let stem = path.with_extension("");
                let relative = stem.strip_prefix(lib).expect("module is under the library");
                out.push(relative.to_string_lossy().replace('\\', "/"));
            }
        }
    }
    out.sort();
    out
}

#[test]
fn the_named_std_prefix_carries_no_postulates_and_restores_a_row_this_bead_names() {
    let lib = lib_or_skip!();
    let root = lib.join(STD_PREFIX);
    if !root.is_dir() {
        // A typed skip that NAMES the missing input, so an absent prefix can
        // never be read as a measured zero.
        eprintln!(
            "SKIP: missing input {} under {} — this lane measures a named Std prefix and \
             does not provision one",
            STD_PREFIX,
            lib.display()
        );
        return;
    }

    let modules = complete_chains_under(&lib, &root);
    // Floors, not golden equalities: more modules at the same Reference epoch is
    // extra coverage, while enumerating fewer than the measured pin must fail.
    assert!(
        modules.len() >= 20,
        "{STD_PREFIX}: expected at least the 20 complete chains measured at the pin, got {}",
        modules.len()
    );

    let mut exported_axioms = 0usize;
    let mut exported_total = 0usize;
    let mut private_total = 0usize;
    let mut residual: Vec<String> = Vec::new();
    let mut lost: Vec<String> = Vec::new();
    for module in &modules {
        let (exported, private) = exported_and_private(&lib, module);
        exported_total += exported.len();
        private_total += private.len();
        for (name, kind) in &exported {
            if !private.contains_key(name) {
                lost.push(format!("{module}::{name}"));
            }
            if *kind == "Axiom" {
                exported_axioms += 1;
                if private.get(name).copied() == Some("Axiom") {
                    residual.push(format!("{module}::{name}"));
                }
            }
        }
    }

    assert!(
        lost.is_empty(),
        "{STD_PREFIX}: the private parts dropped names the exported parts had: {lost:?}"
    );
    // Anti-vacuity for the emptiness claim below. Without this floor the
    // assertion is satisfied by a prefix that never postulated anything, which
    // says nothing at all about the repair.
    assert!(
        exported_axioms >= 3_500,
        "{STD_PREFIX}: expected the exported parts to postulate at least the 3,561 measured at \
         the pin, got {exported_axioms} — a low count makes the empty residual below vacuous"
    );
    assert!(
        private_total > exported_total,
        "{STD_PREFIX}: the private parts are supposed to ADD declarations \
         (exported {exported_total}, private {private_total})"
    );
    // Unlike Init, this prefix has NO real axioms of its own: every one of its
    // postulates is a body the exported part withheld. So the residual is not
    // "the pin's genuine axioms" here — it is empty.
    assert!(
        residual.is_empty(),
        "{STD_PREFIX}: declarations still postulated after the private part was read: {residual:?}"
    );

    let (declaration, module) = STD_NAMED_ROW;
    let (exported, private) = exported_and_private(&lib, module);
    assert_eq!(exported.get(declaration).copied(), Some("Axiom"));
    assert_eq!(
        private.get(declaration).copied(),
        Some("Defn"),
        "{declaration} is one of the four definitions d17i found in BOTH the UnknownConstant and \
         DefinitionTypeMismatch families; the private part must restore its body"
    );
}

/// The four definitions d17i found in BOTH restrictive families, closed.
///
/// The exhaustive pass of 2026-07-25 separated the 13 DefinitionTypeMismatch
/// rows from the 24 UnknownConstant rows and found that four definitions
/// appeared in both: when an un-decoded auxiliary sat in a declaration's own
/// type or body the kernel reported `UnknownConstant`, and when it sat only on
/// the unfolding path `def_eq` needed, the same root cause surfaced as
/// `DefinitionTypeMismatch`. `Lean.Name.beq` showed both at once — `eq_4` and
/// `eq_def` failed one way while `eq_1`, `eq_2` and `eq_3` failed the other.
///
/// That four-definition set is the last named population on this bead without a
/// pin. Earlier increments covered three of them incidentally; none stated the
/// set. All four take the same transition, which is the point: one root cause,
/// one repair, no survivors.
///
/// `Std.Iterators.Types.Attach.Monadic.modifyStep` is the reason this is a
/// table of (declaration, module) pairs rather than a name list. Despite its
/// `Std.` prefix it lives under `Init/Data/Iterators/…` at this pin, so
/// searching the `Std/` subtree for it reports it absent — a false negative
/// that a name-only list would have made permanent.
const CROSS_FAMILY_DEFINITIONS: &[(&str, &str)] = &[
    ("Lean.Name.beq", "Init/Prelude"),
    ("List.toArrayAux", "Init/Data/List/ToArrayImpl"),
    (
        "Std.DHashMap.Internal.AssocList.contains",
        "Std/Data/DHashMap/Internal/AssocList/Basic",
    ),
    (
        "Std.Iterators.Types.Attach.Monadic.modifyStep",
        "Init/Data/Iterators/Combinators/Monadic/Attach",
    ),
];

/// The two auxiliaries d17i names for `modifyStep`, spelled in full. The bead
/// records them as the constants whose absence blocked the unfolding.
const MODIFY_STEP_PROOFS: &[&str] = &[
    "_private.Init.Data.Iterators.Combinators.Monadic.Attach.0.Std.Iterators.Types.Attach.Monadic.modifyStep._proof_1",
    "_private.Init.Data.Iterators.Combinators.Monadic.Attach.0.Std.Iterators.Types.Attach.Monadic.modifyStep._proof_3",
];

#[test]
fn every_definition_that_appeared_in_both_restrictive_families_is_restored() {
    let lib = lib_or_skip!();
    for (declaration, module) in CROSS_FAMILY_DEFINITIONS {
        let (exported, private) = exported_and_private(&lib, module);
        assert_eq!(
            exported.get(*declaration).copied(),
            Some("Axiom"),
            "{declaration}: the exported reading this bead recorded must still be reproducible, \
             or the private reading below is not evidence of a repair"
        );
        assert_eq!(
            private.get(*declaration).copied(),
            Some("Defn"),
            "{declaration}: one of the four cross-family definitions lost its body again"
        );
    }

    let (exported, private) =
        exported_and_private(&lib, "Init/Data/Iterators/Combinators/Monadic/Attach");
    for proof in MODIFY_STEP_PROOFS {
        assert_eq!(
            exported.get(*proof).copied(),
            None,
            "{proof}: absence from the exported part is why modifyStep could not be unfolded"
        );
        assert_eq!(
            private.get(*proof).copied(),
            Some("Thm"),
            "{proof}: the private part must supply the auxiliary the unfolding needed"
        );
    }
}

/// The six `ArtifactIncomplete` rows the Prelude census reports, paired with
/// the auxiliary each one names as missing.
///
/// These six are a live residual of the same part-selection cause, and they are
/// the last one on this bead's spine that is not merely historical: the census
/// reports them TODAY. `decode_prelude` reads `Init/Prelude.olean` alone — the
/// exported part, 2,204 constants — so every private auxiliary those six
/// non-safe implementation helpers reference is absent from the environment the
/// census is handed, and it records six declarations with missing references.
///
/// THE CENSUS IS NOT WRONG. Given an exported-only environment its finding is
/// exactly right, and refusing to report a gap it can see is the last thing we
/// would want it to do. What is incomplete is the INPUT, not the artifact and
/// not the guard. The pairing below is the evidence for that reading: every one
/// of the six declarations is a `Defn` in BOTH parts — their bodies were never
/// missing, so the rows are not about them — while every auxiliary they name is
/// absent from the exported part and present in the private one.
///
/// This is deliberately a measurement and not a repair. Feeding the census the
/// companion chain moves the pinned 2,204 constant census and the pinned
/// six-row expectation together, in a 342KB file several panes are editing;
/// that is a coordinated lane change, not a smallest fix, and it belongs to the
/// census owner rather than here.
const ARTIFACT_INCOMPLETE_ROWS: &[(&str, &str, &str)] = &[
    (
        "Lean.Name.hash._override",
        "_private.Init.Prelude.0.Lean.Name.hash._proof_1",
        "Thm",
    ),
    (
        "Lean.Name.num._override",
        "_private.Init.Prelude.0.Lean.Name.hash._proof_2",
        "Thm",
    ),
    (
        "Lean.Syntax.getHeadInfo?._unsafe_rec",
        "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.match_1",
        "Defn",
    ),
    (
        "Lean.Syntax.getTailPos?._unsafe_rec",
        "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.match_1",
        "Defn",
    ),
    (
        "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
        "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop.match_1",
        "Defn",
    ),
    (
        "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
        "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop.match_1",
        "Defn",
    ),
];

#[test]
fn the_six_artifact_incomplete_rows_name_auxiliaries_the_private_part_supplies() {
    let lib = lib_or_skip!();
    let (exported, private) = exported_and_private(&lib, "Init/Prelude");

    for (declaration, auxiliary, auxiliary_kind) in ARTIFACT_INCOMPLETE_ROWS {
        // The declaration side. A row about a declaration whose own body were
        // missing would be a different finding with a different remedy, so
        // this half is what rules that reading out.
        assert_eq!(
            exported.get(*declaration).copied(),
            Some("Defn"),
            "{declaration}: the census row is not about this declaration being absent"
        );
        assert_eq!(
            private.get(*declaration).copied(),
            Some("Defn"),
            "{declaration}: present with a body at both levels"
        );
        // The reference side, which is what the row is actually about.
        assert_eq!(
            exported.get(*auxiliary).copied(),
            None,
            "{auxiliary}: absence from the exported part is why the census records the row"
        );
        assert_eq!(
            private.get(*auxiliary).copied(),
            Some(*auxiliary_kind),
            "{auxiliary}: the private part supplies it, so the row is a property of the input"
        );
    }

    // Anti-vacuity, and the number the census itself is pinned to. If the
    // exported census ever stops being 2,204 the pairing above is being read
    // against a different artifact than the one the six rows were measured on.
    assert_eq!(
        exported.len(),
        2_204,
        "the exported Prelude census the six ArtifactIncomplete rows were measured against"
    );
    assert!(
        private.len() > exported.len(),
        "the private part must supply more than the exported census (exported {}, private {})",
        exported.len(),
        private.len()
    );
}

/// The CROSS-MODULE half of the UnknownConstant story, which every pin above
/// misses.
///
/// Everything measured so far compares two parts of ONE module. d17i's sharpest
/// structural evidence was not that shape: it observed `Init.Meta.Defs`
/// referencing `_private.Init.Prelude.0.Lean.Name.beq.match_1` while
/// "Init.Prelude was decoded first with 2,204 declarations". That number is the
/// EXPORTED census — pinned as an equality above — so the old run had already
/// processed the owning module and still could not resolve the reference.
///
/// The measurement below says why, and it is a property no within-module pin
/// can state: the auxiliary is absent from BOTH parts of the referencing
/// module. A module never carries another module's private auxiliary just
/// because it uses one. Resolution therefore depends entirely on the OWNING
/// module having been admitted at its private level; decoding the referencing
/// module perfectly cannot help, and neither can the kernel, which can only
/// report a name the environment does not hold.
const CROSS_MODULE_REFERENCE: (&str, &str, &str) = (
    "_private.Init.Prelude.0.Lean.Name.beq.match_1",
    "Init/Meta/Defs", // references it
    "Init/Prelude",   // owns it, at private level only
);

/// A private name's `_private.<Module>.0.` prefix names the module that owns
/// the PRIVACY SCOPE, not the module that stores the declaration.
///
/// This is the trap in the const above, and it is worth a pin of its own
/// because the natural repair for a missing `_private.A.0.x` — go and look in
/// module `A` — is wrong for a real population. `Array.ofFn.go` is private to
/// `Init/Data/Array/Basic`, so lemmas derived from it inherit that scope in
/// their names; but `congr_simp` is GENERATED in the modules that trigger it
/// and is stored there. It is absent from `Init/Data/Array/Basic` at both
/// levels and present in two other modules' private parts.
///
/// Measured across the 600 Init modules carrying a complete chain: 34
/// declarations are stored in a module other than the one their private prefix
/// names. So this is a population, not a curiosity, and a resolver keyed on the
/// prefix silently fails on all of them.
const SCOPE_IS_NOT_STORAGE: (&str, &str, &[&str]) = (
    "_private.Init.Data.Array.Basic.0.Array.ofFn.go.congr_simp",
    "Init/Data/Array/Basic", // names the privacy scope; does NOT store it
    &["Init/Data/Array/Lemmas", "Init/Data/Array/OfFn"], // actually store it
);

#[test]
fn a_private_auxiliary_is_never_carried_by_the_module_that_references_it() {
    let lib = lib_or_skip!();
    let (auxiliary, referencing, owning) = CROSS_MODULE_REFERENCE;

    let (exported, private) = exported_and_private(&lib, referencing);
    assert_eq!(
        exported.get(auxiliary).copied(),
        None,
        "{referencing}: a referencing module does not carry the auxiliary at exported level"
    );
    assert_eq!(
        private.get(auxiliary).copied(),
        None,
        "{referencing}: nor at private level — this is what makes the reference CROSS-module, \
         and what no amount of decoding the referencing module can fix"
    );

    let (exported, private) = exported_and_private(&lib, owning);
    assert_eq!(
        exported.get(auxiliary).copied(),
        None,
        "{owning}: absent from the exported part, which is why processing this module first at \
         2,204 declarations still left the reference unresolved"
    );
    assert_eq!(
        private.get(auxiliary).copied(),
        Some("Defn"),
        "{owning}: the private level is the only place the auxiliary exists, so admitting the \
         OWNING module at private level is the necessary condition for resolution"
    );
}

#[test]
fn a_private_name_prefix_names_the_scope_and_not_the_storing_module() {
    let lib = lib_or_skip!();
    let (declaration, scope_module, storing_modules) = SCOPE_IS_NOT_STORAGE;

    let (exported, private) = exported_and_private(&lib, scope_module);
    assert_eq!(
        exported.get(declaration).copied(),
        None,
        "{scope_module} names the privacy scope but must not store the declaration"
    );
    assert_eq!(
        private.get(declaration).copied(),
        None,
        "{scope_module}: absent at private level too — resolving this name by going to the \
         module its prefix names finds nothing"
    );

    for module in storing_modules {
        let (_, private) = exported_and_private(&lib, module);
        assert_eq!(
            private.get(declaration).copied(),
            Some("Thm"),
            "{module}: generated into the module that triggered it, and stored there"
        );
    }
}

/// `Lean.Name.beq`: one definition, BOTH reject classes, fully accounted for.
///
/// This bead's exhaustive pass found that `eq_4` and `eq_def` failed as
/// `UnknownConstant` while `eq_1`, `eq_2` and `eq_3` failed as
/// `DefinitionTypeMismatch` — the same definition producing both families at
/// once. That split was the evidence for "one root cause, two symptoms", and it
/// is the last named observation on this bead with nothing behind it.
///
/// The measurement resolves it, and the shape is not what the row text
/// suggests. The five equation lemmas were NEVER missing: they live in
/// `Init/Meta/Defs` and are `Thm` in BOTH parts. What was missing were two
/// things owned by a DIFFERENT module, `Init/Prelude`, and neither of them is
/// carried by `Init/Meta/Defs` at either level:
///
///   `Lean.Name.beq`                                   Axiom  -> Defn
///   `_private.Init.Prelude.0.Lean.Name.beq.match_1`   ABSENT -> Defn
///
/// Two different absences, one owning module, two reject classes in a third
/// module whose own declarations were all present. `eq_4` and `eq_def` name the
/// auxiliary in their own statements, so the kernel reported the constant it
/// could not find; `eq_1..eq_3` only need `Lean.Name.beq` to UNFOLD to close an
/// `rfl`, and it was a postulate, so defeq got stuck and the kernel reported a
/// type mismatch. Same repair, because both absences are the exported level.
///
/// Note the privacy scope: the lemmas are `_private.Init.Meta.Defs.0.…` even
/// though they are about a `Prelude` definition — the generated-here rule this
/// file already pins in `SCOPE_IS_NOT_STORAGE`, showing up on the bead's own
/// headline example.
const BEQ_EQUATION_LEMMAS: &[&str] = &[
    "_private.Init.Meta.Defs.0.Lean.Name.beq.eq_1",
    "_private.Init.Meta.Defs.0.Lean.Name.beq.eq_2",
    "_private.Init.Meta.Defs.0.Lean.Name.beq.eq_3",
    "_private.Init.Meta.Defs.0.Lean.Name.beq.eq_4",
    "_private.Init.Meta.Defs.0.Lean.Name.beq.eq_def",
];

#[test]
fn both_reject_classes_for_one_definition_reduce_to_two_absences_in_another_module() {
    let lib = lib_or_skip!();

    // The lemmas themselves, in the module that generated them. Present at BOTH
    // levels: the rows were never about these, and asserting it is what stops
    // "the equation lemmas were missing" from being a plausible reading.
    let (exported, private) = exported_and_private(&lib, "Init/Meta/Defs");
    for lemma in BEQ_EQUATION_LEMMAS {
        assert_eq!(
            exported.get(*lemma).copied(),
            Some("Thm"),
            "{lemma}: present in the exported part, so its rejection was never about its own \
             absence"
        );
        assert_eq!(
            private.get(*lemma).copied(),
            Some("Thm"),
            "{lemma}: and unchanged at private level"
        );
    }

    // Neither missing constant is carried by the module that references them.
    // This is what makes the failure CROSS-module: nothing the referencing
    // module could have decoded better would have supplied either one.
    for absent in [
        "Lean.Name.beq",
        "_private.Init.Prelude.0.Lean.Name.beq.match_1",
    ] {
        assert_eq!(
            exported.get(absent).copied(),
            None,
            "{absent}: Init/Meta/Defs does not own this at exported level"
        );
        assert_eq!(
            private.get(absent).copied(),
            None,
            "{absent}: nor at private level — it belongs to Init/Prelude"
        );
    }

    // The two absences, in the module that does own them, each explaining one
    // of the two reject classes.
    let (exported, private) = exported_and_private(&lib, "Init/Prelude");
    assert_eq!(
        exported.get("Lean.Name.beq").copied(),
        Some("Axiom"),
        "a postulated `Lean.Name.beq` cannot be unfolded, which is the \
         DefinitionTypeMismatch half (eq_1, eq_2, eq_3)"
    );
    assert_eq!(private.get("Lean.Name.beq").copied(), Some("Defn"));
    let auxiliary = "_private.Init.Prelude.0.Lean.Name.beq.match_1";
    assert_eq!(
        exported.get(auxiliary).copied(),
        None,
        "an absent auxiliary named in a lemma's own statement is the \
         UnknownConstant half (eq_4, eq_def)"
    );
    assert_eq!(private.get(auxiliary).copied(), Some("Defn"));
}

/// Every constant `root` references, collected without expanding shared DAGs.
///
/// `allocation_identity` is the in-process node identity provided for exactly
/// this: a bounded walk that visits a shared subterm once. It is not a semantic
/// hash and nothing derived from it is retained.
///
/// The cap PANICS rather than returning what it has. A truncated walk that
/// returned early would answer "this constant is not referenced" for a
/// declaration whose reference simply sat past the cap — and the assertions
/// below turn exactly that answer into a classification. A loud failure asking
/// for a bigger cap is recoverable; a quiet false negative is not.
fn referenced_constants(root: &Expr) -> BTreeSet<String> {
    const CAP: usize = 1_000_000;
    let mut out = BTreeSet::new();
    let mut seen: BTreeSet<usize> = BTreeSet::new();
    let mut stack: Vec<&Expr> = vec![root];
    while let Some(current) = stack.pop() {
        if !seen.insert(current.allocation_identity()) {
            continue;
        }
        assert!(
            seen.len() < CAP,
            "reference walk exceeded {CAP} distinct nodes; raise the cap rather than \
             trusting a truncated answer"
        );
        match current.node() {
            ExprNode::Const { name, .. } => {
                out.insert(name.to_display_string());
            }
            ExprNode::App { f, a } => {
                stack.push(f);
                stack.push(a);
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                stack.push(binder_type);
                stack.push(body);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                stack.push(type_);
                stack.push(value);
                stack.push(body);
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => stack.push(expr),
            ExprNode::BVar { .. }
            | ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Lit { .. } => {}
        }
    }
    out
}

/// Which of `Lean.Name.beq`'s equation lemmas actually REFERENCE the auxiliary
/// that was missing, read from the declarations rather than from a reject log.
///
/// Columns are (lemma, aux-in-type, aux-in-value). Every one of the five also
/// references `Lean.Name.beq` itself, in both type and value, which is why the
/// stripped body alone would have failed all five.
const BEQ_LEMMA_REFERENCES: &[(&str, bool, bool)] = &[
    ("eq_1", false, false),
    ("eq_2", false, false),
    ("eq_3", false, false),
    ("eq_4", false, true),
    ("eq_def", true, true),
];

/// The reject-class discriminator, derived from the bytes.
///
/// The previous increment pinned WHICH constants were absent. It did not
/// establish why the same definition produced two different reject classes —
/// that was still inherited from the 2026-07-25 reject log, and my comment on
/// it said the two `UnknownConstant` rows "name the auxiliary in their own
/// statements". That is wrong for `eq_4`, and this measurement is what shows
/// it: `eq_4` references the auxiliary in its VALUE only, not its type. Only
/// `eq_def` carries it in the statement.
///
/// The rule the data actually supports is that a declaration is reported
/// `UnknownConstant` when the absent constant appears anywhere among its own
/// references — type OR value — and falls through to a defeq failure when it
/// does not. Under that rule the split is exactly reproduced: `eq_4` and
/// `eq_def` reference the auxiliary and were the two `UnknownConstant` rows;
/// `eq_1`, `eq_2` and `eq_3` reference it nowhere and were the three
/// `DefinitionTypeMismatch` rows, failing instead on the postulated
/// `Lean.Name.beq` that all five need to unfold.
#[test]
fn the_reject_class_split_is_predicted_by_each_lemmas_own_references() {
    let lib = lib_or_skip!();
    let base = lib.join("Init/Meta/Defs.olean");
    let read =
        |path: PathBuf| std::fs::read(&path).unwrap_or_else(|e| panic!("read {path:?}: {e}"));
    let exported = read(base.clone());
    let server = read(base.with_extension("olean.server"));
    let private = read(base.with_extension("olean.private"));
    let view = OleanView::parse_with_dependencies(&private, &[&exported, &server])
        .expect("parse private part against its earlier regions");
    let infos = DeclDecoder::new(&view, WalkBudget::default())
        .decode_module_constants()
        .expect("decode private part");

    let auxiliary = "_private.Init.Prelude.0.Lean.Name.beq.match_1";
    for (lemma, in_type, in_value) in BEQ_LEMMA_REFERENCES {
        let name = format!("_private.Init.Meta.Defs.0.Lean.Name.beq.{lemma}");
        let Some(ConstantInfo::Thm(thm)) = infos
            .iter()
            .find(|info| info.name().to_display_string() == name)
        else {
            panic!("{name} must decode as a theorem from the private part");
        };
        let type_refs = referenced_constants(&thm.base.type_);
        let value_refs = referenced_constants(&thm.value);
        assert_eq!(
            type_refs.contains(auxiliary),
            *in_type,
            "{lemma}: auxiliary in the STATEMENT — this is the column that separates eq_def \
             from eq_4, and getting it wrong is what made the earlier account imprecise"
        );
        assert_eq!(
            value_refs.contains(auxiliary),
            *in_value,
            "{lemma}: auxiliary in the PROOF"
        );
        // The common half: every lemma needs `Lean.Name.beq` to unfold, which
        // is why a stripped body alone would have failed all five and cannot by
        // itself explain why only three carried the defeq class.
        assert!(
            type_refs.contains("Lean.Name.beq") && value_refs.contains("Lean.Name.beq"),
            "{lemma}: must reference the definition whose body was stripped"
        );
    }

    // Anti-vacuity: the walker must actually find things. A collector that
    // returned an empty set would satisfy every `false` above.
    let sample = infos
        .iter()
        .find(|info| info.name().to_display_string().ends_with("beq.eq_def"))
        .expect("eq_def decodes");
    assert!(
        referenced_constants(&sample.constant_val().type_).len() > 3,
        "the reference walker must return a non-trivial set, or every negative \
         assertion above is vacuous"
    );
}

/// Every expression a declaration carries: its type, its value where it has
/// one, and a recursor's rule right-hand sides.
///
/// The rule bodies are easy to forget and were the one thing my first pass at
/// this measurement dropped — 129 recursors' worth. A reference scan that
/// silently skips part of its input reports a smaller deficit than the truth
/// and reads as a stronger result, which is the opposite of what a scan owes.
fn declaration_expressions(info: &ConstantInfo) -> Vec<&Expr> {
    let mut out = vec![&info.constant_val().type_];
    match info {
        ConstantInfo::Defn(v) => out.push(&v.value),
        ConstantInfo::Thm(v) => out.push(&v.value),
        ConstantInfo::Opaque(v) => out.push(&v.value),
        ConstantInfo::Rec(v) => out.extend(v.rules.iter().map(|rule| &rule.rhs)),
        ConstantInfo::Axiom(_)
        | ConstantInfo::Quot(_)
        | ConstantInfo::Induct(_)
        | ConstantInfo::Ctor(_) => {}
    }
    out
}

/// Names referenced by the module's declarations that the module does not
/// itself declare.
fn unresolved_references(infos: &[ConstantInfo]) -> (BTreeSet<String>, usize) {
    let declared: BTreeSet<String> = infos
        .iter()
        .map(|info| info.name().to_display_string())
        .collect();
    let mut referenced = BTreeSet::new();
    for info in infos {
        for expr in declaration_expressions(info) {
            referenced.append(&mut referenced_constants(expr));
        }
    }
    let total = referenced.len();
    (referenced.difference(&declared).cloned().collect(), total)
}

/// `Init/Prelude` is reference-CLOSED at private level, and its exported
/// deficit is exactly the six auxiliaries the census reports.
///
/// Every other pin in this file asks whether a NAMED constant is present. This
/// asks the general question the `UnknownConstant` class is actually about:
/// does anything the module references fail to resolve? `Init/Prelude` is the
/// only module where that can be asked without an import closure, because it
/// imports nothing — so every constant it references must be declared by it, or
/// the reference is unresolvable outright.
///
/// The two levels answer differently, which is what makes either answer worth
/// recording:
///
///   exported   2,204 declared, 1,321 referenced, SIX unresolved
///   private    2,314 declared, 1,543 referenced, ZERO unresolved
///
/// The six are not a list this test carries. They are derived here by closure
/// and compared against `ARTIFACT_INCOMPLETE_ROWS`, whose auxiliaries were
/// taken from the census's own rows. Two independent derivations of the same
/// six: the census is not reporting a hand-picked set, it is reporting the
/// exported part's reference deficit, and the private part closes it exactly.
#[test]
fn the_import_free_root_module_is_reference_closed_at_private_level() {
    let lib = lib_or_skip!();
    let base = lib.join("Init/Prelude.olean");
    let read = |p: PathBuf| std::fs::read(&p).unwrap_or_else(|e| panic!("read {p:?}: {e}"));
    let exported = read(base.clone());
    let server = read(base.with_extension("olean.server"));
    let private = read(base.with_extension("olean.private"));

    let exported_view = OleanView::parse(&exported).expect("parse exported part");
    let exported_infos = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .expect("decode exported part");
    let private_view = OleanView::parse_with_dependencies(&private, &[&exported, &server])
        .expect("parse private part");
    let private_infos = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("decode private part");

    let (exported_unresolved, exported_referenced) = unresolved_references(&exported_infos);
    let (private_unresolved, private_referenced) = unresolved_references(&private_infos);

    // Anti-vacuity. A walker that returned nothing would report zero unresolved
    // at BOTH levels and look like the strongest possible result.
    assert!(
        exported_referenced > 1_000 && private_referenced > exported_referenced,
        "the reference scan must actually reach the declarations (exported \
         {exported_referenced}, private {private_referenced})"
    );

    let expected: BTreeSet<String> = ARTIFACT_INCOMPLETE_ROWS
        .iter()
        .map(|(_, auxiliary, _)| (*auxiliary).to_string())
        .collect();
    assert_eq!(
        exported_unresolved, expected,
        "the exported part's reference deficit must be exactly the auxiliaries the census \
         names. These are derived two different ways — by closure here, from the census's own \
         rows there — and a disagreement means one of them is describing something else."
    );
    assert!(
        private_unresolved.is_empty(),
        "the private part must close every reference its declarations make; anything left \
         here is a genuine UnknownConstant source at the root of the corpus: \
         {private_unresolved:?}"
    );
}

/// Which level a module chain is read at.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Level {
    Exported,
    Private,
}

/// Decode one module at the requested level, returning its declarations and
/// the modules it imports.
fn decode_at(lib: &Path, module: &str, level: Level) -> (Vec<ConstantInfo>, Vec<String>) {
    let base = lib.join(format!("{}.olean", module.replace('.', "/")));
    let read = |p: PathBuf| std::fs::read(&p).unwrap_or_else(|e| panic!("read {p:?}: {e}"));
    let exported = read(base.clone());
    let exported_view = OleanView::parse(&exported).expect("parse exported part");
    let imports = exported_view
        .module_data(WalkBudget::default())
        .expect("module data")
        .imports
        .iter()
        .map(|import| import.module.to_display_string())
        .collect();
    let infos = match level {
        Level::Exported => DeclDecoder::new(&exported_view, WalkBudget::default())
            .decode_module_constants()
            .expect("decode exported part"),
        Level::Private => {
            let server = read(base.with_extension("olean.server"));
            let private = read(base.with_extension("olean.private"));
            let view = OleanView::parse_with_dependencies(&private, &[&exported, &server])
                .expect("parse private part");
            DeclDecoder::new(&view, WalkBudget::default())
                .decode_module_constants()
                .expect("decode private part")
        }
    };
    (infos, imports)
}

/// Every name declared by `module` and, transitively, by everything it imports.
///
/// A module whose file is absent would silently shrink the closure and make the
/// deficit below look larger than it is, so misses are counted and the caller
/// asserts there were none rather than trusting the walk to have been complete.
fn closure_declared(lib: &Path, module: &str, level: Level) -> (BTreeSet<String>, usize) {
    let mut declared = BTreeSet::new();
    let mut visited: BTreeSet<String> = BTreeSet::new();
    let mut missing = 0usize;
    let mut queue = vec![module.to_string()];
    while let Some(current) = queue.pop() {
        if !visited.insert(current.clone()) {
            continue;
        }
        let base = lib.join(format!("{}.olean", current.replace('.', "/")));
        if !base.is_file() {
            missing += 1;
            continue;
        }
        let (infos, imports) = decode_at(lib, &current, level);
        declared.extend(infos.iter().map(|info| info.name().to_display_string()));
        queue.extend(imports);
    }
    (declared, missing)
}

/// The cross-module half of the UnknownConstant question.
///
/// `f564f92e` closed it for `Init/Prelude`, which imports nothing — so that
/// result says nothing about a reference that has to cross an import edge, and
/// crossing one is exactly what this bead observed: `Init.Meta.Defs`
/// referencing `_private.Init.Prelude.0.Lean.Name.beq.match_1` while Prelude
/// had already been processed.
///
/// Measured over `Init.Meta.Defs` and its 7 direct imports, transitively:
///
///   exported   8,483 declared in closure, 267 referenced, THREE unresolved
///   private    9,217 declared in closure, 898 referenced, ZERO unresolved
///
/// The three are the whole point, and they are not all the same shape:
///
///   `_private.Init.Prelude.0.Lean.Name.beq.match_1`            owned ELSEWHERE
///   `_private.Init.Meta.Defs.0.Lean.Name.beq.match_1.eq_4`     owned HERE
///   `_private.Init.Meta.Defs.0.Lean.Name.beq.match_1.splitter` owned HERE
///
/// So one module exhibits both failure modes at once: a foreign private
/// auxiliary its import could not supply at exported level, and two of its OWN
/// private auxiliaries absent from its own exported part. Reading the whole
/// closure at private level resolves all three, which is what makes the earlier
/// per-name pins add up to a property rather than a list.
const CROSS_MODULE_DEFICIT: &[&str] = &[
    "_private.Init.Meta.Defs.0.Lean.Name.beq.match_1.eq_4",
    "_private.Init.Meta.Defs.0.Lean.Name.beq.match_1.splitter",
    "_private.Init.Prelude.0.Lean.Name.beq.match_1",
];

#[test]
fn a_module_with_imports_is_reference_closed_only_at_private_level() {
    let lib = lib_or_skip!();
    const MODULE: &str = "Init.Meta.Defs";

    let mut referenced_counts = Vec::new();
    let mut deficits = Vec::new();
    let mut structural_counts = Vec::new();
    for level in [Level::Exported, Level::Private] {
        let (infos, imports) = decode_at(&lib, MODULE, level);
        assert!(
            imports.len() >= 7,
            "{MODULE} is supposed to import at least the 7 measured at the pin, got {}",
            imports.len()
        );
        let (available, missing) = closure_declared(&lib, MODULE, level);
        assert_eq!(
            missing, 0,
            "an absent module would shrink the closure and inflate the deficit"
        );
        let mut referenced = BTreeSet::new();
        for info in &infos {
            for expr in declaration_expressions(info) {
                referenced.append(&mut referenced_constants(expr));
            }
        }
        referenced_counts.push(referenced.len());
        deficits.push(
            referenced
                .difference(&available)
                .cloned()
                .collect::<Vec<_>>(),
        );
        assert!(
            available.len() > 8_000,
            "the import closure must actually be walked, got {} names",
            available.len()
        );

        // The STRUCTURAL surface, over the same closure. `81165464` showed the
        // exported deficit is expression-only for the import-free root; this is
        // the same question one import edge out, and it reuses the closure
        // already computed rather than walking it again.
        let structural: BTreeSet<String> =
            infos.iter().flat_map(structural_name_references).collect();
        structural_counts.push(structural.len());
        let structural_unresolved: Vec<&String> = structural.difference(&available).collect();
        assert!(
            structural_unresolved.is_empty(),
            "block admission resolves these by name across imports too, so an unresolved one              here would be a BlockMismatch the exported level could produce:              {structural_unresolved:?}"
        );
    }

    // Anti-vacuity: an empty reference scan satisfies "zero unresolved".
    assert!(
        referenced_counts[0] > 200 && referenced_counts[1] > referenced_counts[0],
        "reference scan must reach the declarations at both levels: {referenced_counts:?}"
    );
    assert_eq!(
        deficits[0], CROSS_MODULE_DEFICIT,
        "the exported deficit is what makes the private closure below a repair rather than a \
         tautology; it must be exactly these three"
    );
    // Anti-vacuity for the structural half, and the shape that matters: the
    // structural surface resolves at BOTH levels while the expression surface
    // does not, one import edge out exactly as at the root.
    assert!(
        structural_counts[0] > 100 && structural_counts[1] > structural_counts[0],
        "structural scan must reach the declarations at both levels: {structural_counts:?}"
    );
    assert!(
        deficits[1].is_empty(),
        "reading the whole closure at private level must resolve every reference, including \
         the one this bead observed crossing an import edge: {:?}",
        deficits[1]
    );
}

/// The NAME references a declaration carries outside its expressions: mutual
/// sibling lists, an inductive's constructors, a constructor's inductive, a
/// recursor's block and its rules' constructors.
///
/// These are looked up by block admission (the KR-6xx/95x/97x machinery behind
/// the `BlockMismatch` family), not by defeq, and they are a separate
/// resolution surface from anything an `Expr` walk can see.
fn structural_name_references(info: &ConstantInfo) -> Vec<String> {
    let names = |v: &[Name]| v.iter().map(Name::to_display_string).collect::<Vec<_>>();
    match info {
        ConstantInfo::Defn(v) => names(&v.all),
        ConstantInfo::Thm(v) => names(&v.all),
        ConstantInfo::Opaque(v) => names(&v.all),
        ConstantInfo::Induct(v) => {
            let mut out = names(&v.all);
            out.extend(names(&v.ctors));
            out
        }
        ConstantInfo::Ctor(v) => vec![v.induct.to_display_string()],
        ConstantInfo::Rec(v) => {
            let mut out = names(&v.all);
            out.extend(v.rules.iter().map(|rule| rule.ctor.to_display_string()));
            out
        }
        ConstantInfo::Axiom(_) | ConstantInfo::Quot(_) => Vec::new(),
    }
}

/// The exported part is STRUCTURALLY closed while being EXPRESSION-incomplete,
/// and that separation is what keeps this bead's two repaired families apart.
///
/// This corrects the scope of the two closure cells above. They walk `Expr`
/// trees, so "does anything the module references fail to resolve" was too
/// broad a description of what they measured: a declaration also names its
/// mutual siblings, its constructors, its inductive and its rules' constructors,
/// and no expression walk reaches any of those. Measured over `Init/Prelude`,
/// the two surfaces answer differently at the same level:
///
///   exported   1,815 structural references, ZERO unresolved
///              1,321 expression references, SIX unresolved
///   private    2,171 structural references, ZERO unresolved
///              1,543 expression references, ZERO unresolved
///
/// So the exported part's deficit is entirely in EXPRESSIONS — types and bodies
/// mentioning private auxiliaries — and never in the block structure. That is
/// the byte-level counterpart of this bead's own classification finding that
/// zero of the 228 `BlockMismatch` rows were private or equation-family: block
/// admission looks up exactly these structural names, and they were all
/// resolvable even before the companion chain was read. The 228 were an
/// elimination-rule defect; they could not have been a name-resolution one.
#[test]
fn structural_name_references_resolve_at_both_levels_unlike_expression_references() {
    let lib = lib_or_skip!();
    let base = lib.join("Init/Prelude.olean");
    let read = |p: PathBuf| std::fs::read(&p).unwrap_or_else(|e| panic!("read {p:?}: {e}"));
    let exported = read(base.clone());
    let server = read(base.with_extension("olean.server"));
    let private = read(base.with_extension("olean.private"));

    let exported_view = OleanView::parse(&exported).expect("parse exported part");
    let exported_infos = DeclDecoder::new(&exported_view, WalkBudget::default())
        .decode_module_constants()
        .expect("decode exported part");
    let private_view = OleanView::parse_with_dependencies(&private, &[&exported, &server])
        .expect("parse private part");
    let private_infos = DeclDecoder::new(&private_view, WalkBudget::default())
        .decode_module_constants()
        .expect("decode private part");

    for (label, infos, expected_expression_deficit) in [
        ("exported", &exported_infos, 6usize),
        ("private", &private_infos, 0),
    ] {
        let declared: BTreeSet<String> = infos
            .iter()
            .map(|info| info.name().to_display_string())
            .collect();
        let structural: BTreeSet<String> =
            infos.iter().flat_map(structural_name_references).collect();
        // Anti-vacuity: a declaration set with no structural references would
        // trivially resolve, and `Init/Prelude` carries hundreds of blocks.
        assert!(
            structural.len() > 1_000,
            "{label}: expected a large structural reference set, got {}",
            structural.len()
        );
        let unresolved: Vec<&String> = structural.difference(&declared).collect();
        assert!(
            unresolved.is_empty(),
            "{label}: block admission looks these up, so an unresolved one is a BlockMismatch \
             waiting to happen: {unresolved:?}"
        );

        // The contrast, measured on the same declarations at the same level.
        let (expression_deficit, _) = unresolved_references(infos);
        assert_eq!(
            expression_deficit.len(),
            expected_expression_deficit,
            "{label}: the expression surface is the one that moves between levels; if it stops \
             differing from the structural surface, the two families this bead separated have \
             stopped being separable by measurement"
        );
    }
}

/// Every constant reference paired with the NUMBER OF LEVEL ARGUMENTS it is
/// applied to. Same bounded walk as `referenced_constants`, same cap discipline.
fn referenced_constants_with_arity(root: &Expr) -> BTreeSet<(String, usize)> {
    const CAP: usize = 1_000_000;
    let mut out = BTreeSet::new();
    let mut seen: BTreeSet<usize> = BTreeSet::new();
    let mut stack: Vec<&Expr> = vec![root];
    while let Some(current) = stack.pop() {
        if !seen.insert(current.allocation_identity()) {
            continue;
        }
        assert!(seen.len() < CAP, "arity walk exceeded {CAP} distinct nodes");
        match current.node() {
            ExprNode::Const { name, levels } => {
                out.insert((name.to_display_string(), levels.len()));
            }
            ExprNode::App { f, a } => {
                stack.push(f);
                stack.push(a);
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                stack.push(binder_type);
                stack.push(body);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                stack.push(type_);
                stack.push(value);
                stack.push(body);
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => stack.push(expr),
            ExprNode::BVar { .. }
            | ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Lit { .. } => {}
        }
    }
    out
}

/// The OTHER half of KR-105, which every closure cell above leaves unmeasured.
///
/// `RejectClass::UnknownConstant` covers two failures, and its own doc says so:
/// "unknown constant, OR level-arity mismatch". Everything pinned above answers
/// the first — is the name resolvable — and nothing answers the second. The two
/// are not interchangeable: a name that resolves perfectly but is applied to the
/// wrong number of universe arguments lands in the same reject class, and the
/// pin's `is_delta` refuses to unfold on exactly that condition
/// (`length(const_levels(f)) == info->get_num_lparams()`).
///
/// Measured over `Init/Prelude` at private level: 1,543 distinct constant
/// references, ZERO applied at an arity other than their declaration's
/// level-parameter count.
///
/// A second fact falls out and is asserted because it is stronger than the
/// first: the number of distinct `(name, arity)` pairs EQUALS the number of
/// distinct names, so every referenced constant is used at exactly one arity
/// throughout the module. A name appearing at two arities would mean at least
/// one site is wrong even if each site individually matched something.
#[test]
fn every_constant_reference_matches_its_declarations_level_arity() {
    let lib = lib_or_skip!();
    let base = lib.join("Init/Prelude.olean");
    let read = |p: PathBuf| std::fs::read(&p).unwrap_or_else(|e| panic!("read {p:?}: {e}"));
    let exported = read(base.clone());
    let server = read(base.with_extension("olean.server"));
    let private = read(base.with_extension("olean.private"));
    let view = OleanView::parse_with_dependencies(&private, &[&exported, &server])
        .expect("parse private part");
    let infos = DeclDecoder::new(&view, WalkBudget::default())
        .decode_module_constants()
        .expect("decode private part");

    let declared_arity: BTreeMap<String, usize> = infos
        .iter()
        .map(|info| {
            (
                info.name().to_display_string(),
                info.constant_val().level_params.len(),
            )
        })
        .collect();

    let mut uses: BTreeSet<(String, usize)> = BTreeSet::new();
    for info in &infos {
        for expr in declaration_expressions(info) {
            uses.append(&mut referenced_constants_with_arity(expr));
        }
    }

    // Anti-vacuity. If every use site were monomorphic the comparison would be
    // 0 == 0 everywhere and would catch nothing; the pin's Prelude is heavily
    // level-polymorphic, up to seven universe arguments at a single site.
    let polymorphic = uses.iter().filter(|(_, arity)| *arity > 0).count();
    assert!(
        polymorphic > 900,
        "expected a level-polymorphic corpus, got {polymorphic} polymorphic use sites of {}",
        uses.len()
    );

    let mismatched: Vec<String> = uses
        .iter()
        .filter_map(|(name, arity)| {
            declared_arity
                .get(name)
                .filter(|declared| *declared != arity)
                .map(|declared| format!("{name}: used with {arity}, declared {declared}"))
        })
        .collect();
    assert!(
        mismatched.is_empty(),
        "a resolvable name at the wrong universe arity is an UnknownConstant row just as much \
         as a missing one, and the pin refuses to delta-unfold on exactly this condition: \
         {mismatched:?}"
    );

    let distinct_names: BTreeSet<&String> = uses.iter().map(|(name, _)| name).collect();
    assert_eq!(
        uses.len(),
        distinct_names.len(),
        "some constant is referenced at two different arities in one module; at least one of \
         those sites is wrong even though each resolves"
    );
}

/// The two recursors whose rules are NOT their block's constructors, named.
///
/// `Lean.Syntax` is a nested inductive (`num_nested = 2`), and a nested block
/// generates auxiliary recursors over the NESTING CONTAINERS: `rec_1`'s rules
/// are `Array`'s constructors and `rec_2`'s are `List`'s. That is correct, and
/// it is the reason the equality below cannot simply be asserted for all 129.
///
/// They are pinned by NAME rather than excluded as a class. "Skip recursors
/// whose block is nested" would be satisfied by any future nested block whose
/// rules were genuinely wrong, and this file has already been bitten twice by
/// scans that quietly dropped part of their input.
const NESTED_AUXILIARY_RECURSORS: &[&str] = &["Lean.Syntax.rec_1", "Lean.Syntax.rec_2"];

/// Decoded block relations agree with each other, which is the surface directly
/// upstream of the `BlockMismatch` family.
///
/// The structural-closure cell asks whether a block's names RESOLVE. It does not
/// ask whether they agree: a constructor could name an inductive whose `ctors`
/// list omits it, or a recursor could carry rules for constructors that are not
/// its block's, and every name involved would still resolve. Block admission
/// regenerates a recursor and compares it against the decoded one, so a decode
/// that got these relations wrong surfaces as exactly the class this bead's 228
/// rows carried.
///
/// Measured over `Init/Prelude` at private level: 127 inductives, 157
/// constructors, 129 recursors; zero round-trip violations; and every recursor's
/// rule set equal to its block's constructors except the two nested auxiliaries
/// above.
#[test]
fn decoded_block_relations_agree_with_each_other() {
    let lib = lib_or_skip!();
    let base = lib.join("Init/Prelude.olean");
    let read = |p: PathBuf| std::fs::read(&p).unwrap_or_else(|e| panic!("read {p:?}: {e}"));
    let exported = read(base.clone());
    let server = read(base.with_extension("olean.server"));
    let private = read(base.with_extension("olean.private"));
    let view = OleanView::parse_with_dependencies(&private, &[&exported, &server])
        .expect("parse private part");
    let infos = DeclDecoder::new(&view, WalkBudget::default())
        .decode_module_constants()
        .expect("decode private part");

    let mut inductives: BTreeMap<String, (&InductiveVal, BTreeSet<String>)> = BTreeMap::new();
    let mut constructors: BTreeMap<String, String> = BTreeMap::new();
    let mut recursors: Vec<(String, &RecursorVal)> = Vec::new();
    for info in &infos {
        let name = info.name().to_display_string();
        match info {
            ConstantInfo::Induct(v) => {
                let ctors = v.ctors.iter().map(Name::to_display_string).collect();
                inductives.insert(name, (v, ctors));
            }
            ConstantInfo::Ctor(v) => {
                constructors.insert(name, v.induct.to_display_string());
            }
            ConstantInfo::Rec(v) => recursors.push((name, v)),
            _ => {}
        }
    }
    assert!(
        inductives.len() > 100 && constructors.len() > 120 && recursors.len() > 100,
        "expected the pin's block census ({} inductives, {} constructors, {} recursors)",
        inductives.len(),
        constructors.len(),
        recursors.len()
    );

    // Round trip, both directions. Either alone is satisfiable by a decode that
    // dropped entries from the other side.
    for (ctor, induct) in &constructors {
        let Some((_, ctors)) = inductives.get(induct) else {
            panic!("{ctor} names `{induct}` as its inductive, which is not one");
        };
        assert!(
            ctors.contains(ctor),
            "{ctor} claims `{induct}`, whose ctors list omits it"
        );
    }
    for (induct, (_, ctors)) in &inductives {
        for ctor in ctors {
            assert_eq!(
                constructors.get(ctor),
                Some(induct),
                "`{induct}` lists {ctor} as a constructor, which does not point back"
            );
        }
    }

    // Recursor rules against the block's constructors, with every recursor
    // accounted for and the exceptions named rather than skipped by shape.
    let mut exceptions: Vec<String> = Vec::new();
    for (name, rec) in &recursors {
        let mut block_ctors: BTreeSet<String> = BTreeSet::new();
        for type_name in &rec.all {
            let key = type_name.to_display_string();
            let Some((_, ctors)) = inductives.get(&key) else {
                panic!("{name} names `{key}` in its block, which is not a decoded inductive");
            };
            block_ctors.extend(ctors.iter().cloned());
        }
        let rule_ctors: BTreeSet<String> = rec
            .rules
            .iter()
            .map(|rule| rule.ctor.to_display_string())
            .collect();
        if rule_ctors != block_ctors {
            exceptions.push(name.clone());
            // An exception must be a NESTED block, or it is simply wrong.
            assert!(
                rec.all.iter().any(|t| inductives
                    .get(&t.to_display_string())
                    .is_some_and(|(v, _)| v.num_nested > 0)),
                "{name}'s rules are not its block's constructors and its block is not nested"
            );
        }
    }
    // Decode order is not a pin law: these are collected by walking the
    // module's constant array, and the artifact is free to order it any way.
    // Compare as a set, keeping the equality so a new member still fails.
    exceptions.sort();
    assert_eq!(
        exceptions, NESTED_AUXILIARY_RECURSORS,
        "the set of recursors whose rules differ from their block's constructors must be \
         exactly the named nested auxiliaries; a new member is a decode defect wearing their \
         clothes"
    );
}

/// The `Lean.Syntax` recursors, whose NUMERIC observables count the
/// nested-expanded block rather than the `all` list.
///
/// `Lean.Syntax` nests `Array` and `List`, so its recursors carry three motives
/// — one per type in the expanded block — while `all` names one. `Lean.Syntax.rec`
/// additionally carries seven minor premises for the expanded block's seven
/// constructors, even though its own `rules` list holds only `Syntax`'s four;
/// the auxiliary types' rules live on `rec_1` and `rec_2`. Named, not excluded
/// by shape, for the same reason as `NESTED_AUXILIARY_RECURSORS`.
const NESTED_NUMERIC_EXCEPTIONS: &[&str] =
    &["Lean.Syntax.rec", "Lean.Syntax.rec_1", "Lean.Syntax.rec_2"];

/// Recursors carrying the K flag at the pin, and the control that shows why.
const K_RECURSORS: &[&str] = &["Eq.rec", "HEq.rec", "True.rec"];

/// The NUMERIC half of the block-observable surface.
///
/// `71f8e0fa` checked the NAME relations — which constructor belongs to which
/// inductive, which rules a recursor carries. Block admission also regenerates
/// and compares `num_params`, `num_indices`, `num_motives`, `num_minors` and
/// `k`, and a decode that got any of those wrong is a `BlockMismatch` with every
/// name still agreeing. Nothing was on that surface.
///
/// Measured over `Init/Prelude` at private level: every constructor's
/// `num_params` equals its inductive's, and every recursor's `num_params`,
/// `num_indices`, `num_motives` and `num_minors` agree with its block, except
/// the three `Lean.Syntax` recursors above.
///
/// THE K FLAG IS THE SHARPER RESULT. It is set for exactly three recursors —
/// `Eq`, `HEq`, `True` — and `PUnit` is the control: `PUnit` is also a
/// single-constructor zero-field inductive and its recursor has `k` CLEAR,
/// because K conversion additionally requires the type to be a Prop. That
/// asymmetry is why `Acc` cannot be K-reduced either (a Prop, single
/// constructor, but its constructor has a field), which is the fact the
/// theorem-unfold repair at `e7cdcbbc` turns on. Asserting the K population as
/// an equality keeps that reasoning anchored to the artifact rather than to a
/// comment.
#[test]
fn numeric_block_observables_agree_and_the_k_population_is_exact() {
    let lib = lib_or_skip!();
    let base = lib.join("Init/Prelude.olean");
    let read = |p: PathBuf| std::fs::read(&p).unwrap_or_else(|e| panic!("read {p:?}: {e}"));
    let exported = read(base.clone());
    let server = read(base.with_extension("olean.server"));
    let private = read(base.with_extension("olean.private"));
    let view = OleanView::parse_with_dependencies(&private, &[&exported, &server])
        .expect("parse private part");
    let infos = DeclDecoder::new(&view, WalkBudget::default())
        .decode_module_constants()
        .expect("decode private part");

    let mut inductives: BTreeMap<String, &InductiveVal> = BTreeMap::new();
    let mut constructors: BTreeMap<String, &ConstructorVal> = BTreeMap::new();
    let mut recursors: Vec<(String, &RecursorVal)> = Vec::new();
    for info in &infos {
        let name = info.name().to_display_string();
        match info {
            ConstantInfo::Induct(v) => drop(inductives.insert(name, v)),
            ConstantInfo::Ctor(v) => drop(constructors.insert(name, v)),
            ConstantInfo::Rec(v) => recursors.push((name, v)),
            _ => {}
        }
    }

    for (name, ctor) in &constructors {
        let induct = inductives
            .get(&ctor.induct.to_display_string())
            .expect("constructor's inductive decodes");
        assert_eq!(
            ctor.num_params, induct.num_params,
            "{name} disagrees with its inductive on the parameter count"
        );
    }

    let mut numeric_exceptions: Vec<String> = Vec::new();
    for (name, rec) in &recursors {
        let types: Vec<&InductiveVal> = rec
            .all
            .iter()
            .map(|t| {
                *inductives
                    .get(&t.to_display_string())
                    .expect("recursor's block type decodes")
            })
            .collect();
        let head = types[0];
        let block_ctors: BTreeSet<String> = types
            .iter()
            .flat_map(|t| t.ctors.iter().map(Name::to_display_string))
            .collect();
        // These two hold for every recursor including the nested ones.
        assert_eq!(rec.num_params, head.num_params, "{name}: num_params");
        assert_eq!(rec.num_indices, head.num_indices, "{name}: num_indices");

        let motives_agree = rec.num_motives as usize == types.len();
        let minors_agree = rec.num_minors as usize == block_ctors.len();
        if !(motives_agree && minors_agree) {
            numeric_exceptions.push(name.clone());
            assert!(
                types.iter().any(|t| t.num_nested > 0),
                "{name}'s motive or minor count does not match its block, and the block is not \
                 nested — that is a BlockMismatch, not a nesting artifact"
            );
        }
    }
    // Sorted for the same reason as above; a batch run caught this one
    // reporting the same three names in a different order.
    numeric_exceptions.sort();
    assert_eq!(
        numeric_exceptions, NESTED_NUMERIC_EXCEPTIONS,
        "the recursors whose numeric observables count an expanded block must be exactly the \
         named nested ones"
    );

    let mut k_set: Vec<String> = recursors
        .iter()
        .filter(|(_, rec)| rec.k)
        .map(|(name, _)| name.clone())
        .collect();
    // Sorted: membership is the claim, not the array's order.
    k_set.sort();
    assert_eq!(
        k_set, K_RECURSORS,
        "K conversion is available for exactly these recursors at the pin"
    );
    // The control. Single constructor, zero fields, and K is still CLEAR —
    // because the type is not a Prop. Without this the K assertion above reads
    // as "single ctor with no fields", which is the wrong rule and the reason
    // `Acc` is not K-reducible.
    let punit = inductives.get("PUnit").expect("PUnit decodes");
    assert_eq!(punit.ctors.len(), 1);
    assert_eq!(
        constructors
            .get(&punit.ctors[0].to_display_string())
            .expect("PUnit.unit decodes")
            .num_fields,
        0
    );
    let (_, punit_rec) = recursors
        .iter()
        .find(|(name, _)| name == "PUnit.rec")
        .expect("PUnit.rec decodes");
    assert!(
        !punit_rec.k,
        "PUnit is single-constructor and zero-field yet must NOT carry K, because it is not a \
         Prop; if this ever flips, the rule being tested above has been misread"
    );
}

/// The last two stored block relations nothing checks: a rule's field count
/// against its constructor's, and a constructor's index against its position.
///
/// `71f8e0fa` checked WHICH constructor each rule names and `cd572cac` checked
/// the recursor's aggregate counts. Neither looks inside a rule. A recursor rule
/// stores `nfields` — how many arguments the minor premise consumes — and a
/// constructor stores `cidx`, its ordinal in its inductive. Block admission
/// regenerates both and compares, so either being wrong is a `BlockMismatch`
/// while every name agrees, every aggregate count agrees, and every cell above
/// this one stays green.
///
/// Measured over `Init/Prelude` at private level: 160 rules, every `nfields`
/// equal to its constructor's `num_fields`, and every `cidx` equal to the
/// constructor's position in its inductive's `ctors` list.
///
/// Both are checked against a floor, because both are the kind of field a
/// broken decode would most plausibly return as a uniform zero: 143 of the 160
/// rules bind at least one field, and the largest `cidx` at the pin is 12, so
/// neither assertion can be satisfied by an all-zeros read.
#[test]
fn recursor_rule_arities_and_constructor_indices_match_their_declarations() {
    let lib = lib_or_skip!();
    let base = lib.join("Init/Prelude.olean");
    let read = |p: PathBuf| std::fs::read(&p).unwrap_or_else(|e| panic!("read {p:?}: {e}"));
    let exported = read(base.clone());
    let server = read(base.with_extension("olean.server"));
    let private = read(base.with_extension("olean.private"));
    let view = OleanView::parse_with_dependencies(&private, &[&exported, &server])
        .expect("parse private part");
    let infos = DeclDecoder::new(&view, WalkBudget::default())
        .decode_module_constants()
        .expect("decode private part");

    let mut inductives: BTreeMap<String, &InductiveVal> = BTreeMap::new();
    let mut constructors: BTreeMap<String, &ConstructorVal> = BTreeMap::new();
    let mut recursors: Vec<(String, &RecursorVal)> = Vec::new();
    for info in &infos {
        let name = info.name().to_display_string();
        match info {
            ConstantInfo::Induct(v) => drop(inductives.insert(name, v)),
            ConstantInfo::Ctor(v) => drop(constructors.insert(name, v)),
            ConstantInfo::Rec(v) => recursors.push((name, v)),
            _ => {}
        }
    }

    let mut rules_seen = 0usize;
    let mut rules_binding_fields = 0usize;
    for (name, rec) in &recursors {
        for rule in &rec.rules {
            rules_seen += 1;
            let ctor_name = rule.ctor.to_display_string();
            let ctor = constructors.get(&ctor_name).unwrap_or_else(|| {
                panic!("{name} has a rule for {ctor_name}, which is not a decoded constructor")
            });
            assert_eq!(
                rule.nfields, ctor.num_fields,
                "{name}'s rule for {ctor_name} binds {} fields, but the constructor declares {}",
                rule.nfields, ctor.num_fields
            );
            if rule.nfields > 0 {
                rules_binding_fields += 1;
            }
        }
    }
    assert!(
        rules_seen >= 150 && rules_binding_fields >= 100,
        "the rule scan must reach the pin's rules and most of them bind fields \
         ({rules_seen} rules, {rules_binding_fields} binding at least one)"
    );

    let mut largest_index = 0u32;
    for (name, ctor) in &constructors {
        let induct = inductives
            .get(&ctor.induct.to_display_string())
            .expect("constructor's inductive decodes");
        let position = induct
            .ctors
            .iter()
            .position(|c| c.to_display_string() == *name)
            .unwrap_or_else(|| panic!("{name} is absent from its inductive's ctors list"));
        assert_eq!(
            ctor.cidx as usize, position,
            "{name} stores index {} but sits at position {position}",
            ctor.cidx
        );
        largest_index = largest_index.max(ctor.cidx);
    }
    assert!(
        largest_index >= 10,
        "a decode returning a uniform zero index would satisfy the check above for every \
         single-constructor type; the pin reaches {largest_index}"
    );
}

/// The quotient constants and the kind each carries.
///
/// `QuotKind` is a stored byte nothing in this file has ever read, and it is
/// dispatched on at reduction time: `quot_reduce_rec` locates the `Quot.mk`
/// argument at position 5 for `Lift` and position 4 for `Ind`. A `Lift`/`Ind`
/// swap would therefore not fail to decode and would not fail to resolve — it
/// would reduce at the wrong argument positions, silently, on every quotient in
/// the corpus. The four constants and their four kinds are a bijection at the
/// pin, so the pin is an equality rather than a containment.
const QUOTIENT_CONSTANTS: &[(&str, QuotKind)] = &[
    ("Quot", QuotKind::Type),
    ("Quot.ind", QuotKind::Ind),
    ("Quot.lift", QuotKind::Lift),
    ("Quot.mk", QuotKind::Ctor),
];

#[test]
fn the_four_quotient_constants_carry_four_distinct_kinds() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut found: Vec<(String, QuotKind)> = infos
        .iter()
        .filter_map(|info| match info {
            ConstantInfo::Quot(v) => Some((info.name().to_display_string(), v.kind)),
            _ => None,
        })
        .collect();
    // Sorted by name: the pin's constant array does not list these
    // alphabetically, so an order-sensitive comparison would fail on a
    // correct decode.
    found.sort_by(|a, b| a.0.cmp(&b.0));
    let expected: Vec<(String, QuotKind)> = QUOTIENT_CONSTANTS
        .iter()
        .map(|(name, kind)| ((*name).to_string(), *kind))
        .collect();
    assert_eq!(
        found, expected,
        "the quotient constants and their kinds are what `quot_reduce_rec` dispatches on"
    );

    // Bijection, stated separately: four constants carrying the same kind twice
    // would still satisfy a per-name check written against a wrong table.
    let kinds: BTreeSet<String> = found.iter().map(|(_, k)| format!("{k:?}")).collect();
    assert_eq!(
        kinds.len(),
        4,
        "each quotient constant must carry a distinct kind"
    );
}

/// Safety flags agree wherever the artifact stores them twice, and the non-safe
/// population is real rather than a decode returning a default.
///
/// `is_unsafe` and `DefinitionSafety` are stored bytes nothing in this file
/// reads. They are load-bearing twice over: KR-973 refuses a safe context that
/// references an unsafe declaration, and the delta gate repaired at `e7cdcbbc`
/// keeps its safety refusal on the `Defn` arm, so a definition decoded with the
/// wrong safety either becomes unfoldable when it must not be or stops being
/// unfoldable when it should be.
///
/// Measured over `Init/Prelude` at private level: 1,677 `Safe`, 32 `Partial`,
/// 11 `Unsafe` definitions, and zero disagreements between a constructor and
/// its inductive or a recursor and its block.
///
/// The census floors matter more than the agreement here. Every constructor and
/// recursor in this module is safe, so the agreement check alone is satisfied by
/// a decode that returned `false` for every `is_unsafe` byte it ever read — and
/// the same uniform-default failure would make every definition look `Safe`.
/// Requiring a real `Partial` and a real `Unsafe` population is what rules that
/// out.
#[test]
fn safety_flags_agree_where_stored_twice_and_the_non_safe_population_is_real() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut inductives: BTreeMap<String, &InductiveVal> = BTreeMap::new();
    let mut safe = 0usize;
    let mut partial = 0usize;
    let mut unsafe_defs = 0usize;
    for info in &infos {
        match info {
            ConstantInfo::Induct(v) => drop(inductives.insert(info.name().to_display_string(), v)),
            ConstantInfo::Defn(v) => match v.safety {
                DefinitionSafety::Safe => safe += 1,
                DefinitionSafety::Partial => partial += 1,
                DefinitionSafety::Unsafe => unsafe_defs += 1,
            },
            _ => {}
        }
    }
    assert!(
        safe > 1_000 && partial >= 30 && unsafe_defs >= 10,
        "the pin carries a real non-safe population; a decode defaulting every safety byte \
         would report all-safe and pass every agreement check below \
         (safe {safe}, partial {partial}, unsafe {unsafe_defs})"
    );

    for info in &infos {
        let name = info.name().to_display_string();
        match info {
            ConstantInfo::Ctor(v) => {
                let induct = inductives
                    .get(&v.induct.to_display_string())
                    .expect("constructor's inductive decodes");
                assert_eq!(
                    v.is_unsafe, induct.is_unsafe,
                    "{name} and its inductive disagree on safety"
                );
            }
            ConstantInfo::Rec(v) => {
                for type_name in &v.all {
                    let induct = inductives
                        .get(&type_name.to_display_string())
                        .expect("recursor's block type decodes");
                    assert_eq!(
                        v.is_unsafe,
                        induct.is_unsafe,
                        "{name} and block member {} disagree on safety",
                        type_name.to_display_string()
                    );
                }
            }
            _ => {}
        }
    }
}

/// `Init/Prelude` decoded at private level — the subject of the cells below.
fn decode_prelude_private(lib: &Path) -> Vec<ConstantInfo> {
    let base = lib.join("Init/Prelude.olean");
    let read = |p: PathBuf| std::fs::read(&p).unwrap_or_else(|e| panic!("read {p:?}: {e}"));
    let exported = read(base.clone());
    let server = read(base.with_extension("olean.server"));
    let private = read(base.with_extension("olean.private"));
    let view = OleanView::parse_with_dependencies(&private, &[&exported, &server])
        .expect("parse private part");
    DeclDecoder::new(&view, WalkBudget::default())
        .decode_module_constants()
        .expect("decode private part")
}

/// Definitions whose stored height does NOT exceed the tallest `Regular`
/// definition their value references.
///
/// UNADJUDICATED. These are named so a fifth one fails, not because they are
/// known to be correct. Three are structure-instance definitions sitting at
/// height 1 over much taller bodies — `Lean.Name.instBEq` (1) over
/// `Lean.Name.beq` (11), `Lean.instHashableName` (1) over `Lean.Name.hash` (7),
/// `Lean.Macro.instInhabitedState` (1) over its own `.default` (2) — and the
/// fourth does not fit that shape at all: `Lean.Name.append` stores 12 while
/// referencing `Lean.extractMacroScopes` at 14.
///
/// These are the rows whose height is at or BELOW the tallest reference, which
/// is the direction that matters: lazy delta unfolds the taller side first, so
/// a height failing to dominate its dependencies inverts the intended order.
/// Heights that merely OVERSHOOT the exact successor are a different and
/// harmless case, deliberately not listed: `Nat.div.go` and `Nat.modCore.go`
/// store 5 over a tallest reference of 2, which is what well-founded recursion
/// auxiliaries do.
///
/// THE DISCRIMINATING CHECK, which I could not run here: ask the pinned Lean
/// binary for these four constants' `ReducibilityHints` and compare. If the pin
/// reports the same values, the height invariant simply is not universal and
/// this list is a fact about Lean; if it reports different ones, decode is
/// misreading the hint word and that is a defect for `fln-olean`. Nothing in
/// this file can tell those apart, and asserting the list either way would be
/// claiming an answer I do not have.
const UNADJUDICATED_HEIGHT_ROWS: &[&str] = &[
    "Lean.Macro.instInhabitedState",
    "Lean.Name.append",
    "Lean.Name.instBEq",
    "Lean.instHashableName",
];

/// `ReducibilityHints` — the stored field that drives unfolding ORDER, and the
/// last one in a `ConstantInfo` that nothing here reads.
///
/// `definition_height` consumes it directly: `Regular(h)` returns `h`, `Abbrev`
/// returns `u32::MAX`, `Opaque` returns 0. Those numbers decide which side lazy
/// delta unfolds first, so a mis-decoded hint does not fail to resolve and does
/// not fail to typecheck — it changes reduction ORDER across the whole corpus.
/// It is also the field immediately beside the `Thm` arm added at `e7cdcbbc`,
/// which is a good reason to have it measured rather than assumed.
///
/// Measured over `Init/Prelude` at private level: 1,171 `Abbrev`, 511
/// `Regular`, 38 `Opaque`; heights spanning 1 through 17 with every value in
/// that range present; and of the 291 definitions whose value references another
/// `Regular` definition, 285 hit Lean's height invariant `h == 1 + max`
/// exactly, 2 overshoot it, and the 4 rows above are the only ones that fail to
/// dominate their references at all.
#[test]
fn reducibility_hints_decode_across_all_three_shapes_and_respect_the_height_invariant() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut heights: BTreeMap<String, u32> = BTreeMap::new();
    let mut abbrev = 0usize;
    let mut opaque = 0usize;
    let mut values: BTreeMap<String, &Expr> = BTreeMap::new();
    for info in &infos {
        if let ConstantInfo::Defn(v) = info {
            let name = info.name().to_display_string();
            match v.hints {
                ReducibilityHints::Regular(h) => drop(heights.insert(name.clone(), h)),
                ReducibilityHints::Abbrev => abbrev += 1,
                ReducibilityHints::Opaque => opaque += 1,
            }
            values.insert(name, &v.value);
        }
    }

    // All three shapes must actually occur. A decoder that returned one constant
    // hint for everything would satisfy every comparison below.
    assert!(
        abbrev > 500 && heights.len() > 300 && opaque > 10,
        "the pin exercises all three hint shapes ({abbrev} abbrev, {} regular, {opaque} opaque)",
        heights.len()
    );
    let distinct: BTreeSet<u32> = heights.values().copied().collect();
    assert!(
        distinct.len() >= 15 && *distinct.iter().next().expect("nonempty") == 1,
        "heights must be a real range starting at 1, got {} distinct values",
        distinct.len()
    );

    let mut departures: Vec<String> = Vec::new();
    let mut compared = 0usize;
    let mut exact = 0usize;
    for (name, height) in &heights {
        let referenced = referenced_constants(values[name]);
        let tallest = referenced
            .iter()
            .filter_map(|r| heights.get(r))
            .copied()
            .max();
        let Some(tallest) = tallest else { continue };
        compared += 1;
        if *height <= tallest {
            departures.push(name.clone());
        } else if *height == tallest + 1 {
            exact += 1;
        }
    }
    assert!(
        compared > 250,
        "the height invariant must be exercised over the pin's definitions, got {compared}"
    );
    // Floor, not an equality: a height that OVERSHOOTS still dominates its
    // references, so it is not an anomaly, and pinning it as one would make
    // well-founded-recursion auxiliaries look like defects.
    assert!(
        exact >= 280,
        "most definitions should sit exactly one above their tallest reference, got {exact} of {compared}"
    );
    // Sorted: collected by walking a BTreeMap, but the table is the claim.
    departures.sort();
    assert_eq!(
        departures, UNADJUDICATED_HEIGHT_ROWS,
        "the definitions departing from `height == 1 + max referenced height` are an open \
         question, not a cleared one. A NEW name here needs adjudicating against the pinned \
         binary before it is added; a name disappearing means the invariant tightened and the \
         list should shrink."
    );
}

/// The recursive inductives at the pin, and the flag that says so.
const RECURSIVE_INDUCTIVES: &[&str] = &[
    "Lean.Name",
    "Lean.ParserDescr",
    "Lean.Syntax",
    "List",
    "Nat",
    "Nat.le",
    "Nat.le.below",
];

/// `is_rec` — a stored flag nothing reads, checked against a property DERIVED
/// from the constructors rather than against a table alone.
///
/// It decides recursor shape: a recursive block's minor premises carry
/// induction hypotheses, so a wrong flag produces a regenerated recursor that
/// differs from the decoded one — a `BlockMismatch`, with every name, count and
/// relation this file already pins still agreeing.
///
/// The derivation is the point. A constructor's type ALWAYS mentions its own
/// inductive, in the result, so "the constructor type references the block" is
/// true for every inductive and would be a check that cannot fail. The property
/// that actually distinguishes them is a recursive occurrence in a FIELD: strip
/// the block's `num_params` leading binders, then look for a block member in the
/// remaining binders' DOMAINS. Measured that way, `is_rec` agrees with the
/// derivation for all 127 inductives in `Init/Prelude`, 7 recursive and 120 not.
///
/// `is_reflexive` is deliberately NOT asserted here. Every inductive in this
/// module carries it false, so any assertion about it would be a vacuous zero;
/// binding it needs a module that actually contains a reflexive type, and
/// pretending otherwise would put a green where there is no evidence.
#[test]
fn the_recursive_flag_matches_a_recursive_occurrence_in_a_constructor_field() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut inductives: BTreeMap<String, &InductiveVal> = BTreeMap::new();
    let mut constructors: BTreeMap<String, &ConstructorVal> = BTreeMap::new();
    for info in &infos {
        match info {
            ConstantInfo::Induct(v) => drop(inductives.insert(info.name().to_display_string(), v)),
            ConstantInfo::Ctor(v) => drop(constructors.insert(info.name().to_display_string(), v)),
            _ => {}
        }
    }

    let mut flagged: Vec<String> = Vec::new();
    for (name, induct) in &inductives {
        let block: BTreeSet<String> = induct.all.iter().map(Name::to_display_string).collect();
        let mut occurs = false;
        for ctor_name in &induct.ctors {
            let ctor = constructors
                .get(&ctor_name.to_display_string())
                .expect("constructor decodes");
            // Walk the Pi spine, skipping the block's parameters; a recursive
            // occurrence is a block member in a remaining binder's DOMAIN. The
            // RESULT is excluded by construction, which is what stops this from
            // being true for every inductive.
            let mut current = &ctor.base.type_;
            let mut depth = 0usize;
            while let ExprNode::ForallE {
                binder_type, body, ..
            } = current.node()
            {
                if depth >= induct.num_params as usize
                    && !referenced_constants(binder_type).is_disjoint(&block)
                {
                    occurs = true;
                    break;
                }
                depth += 1;
                current = body;
            }
            if occurs {
                break;
            }
        }
        assert_eq!(
            induct.is_rec, occurs,
            "{name}: stored is_rec={} but a recursive occurrence in a constructor field is {occurs}",
            induct.is_rec
        );
        if induct.is_rec {
            flagged.push(name.clone());
        }
    }

    // Both populations must be real. An all-false decode would satisfy the
    // agreement above for every non-recursive type, which is most of them.
    assert!(
        inductives.len() - flagged.len() > 100,
        "expected a large non-recursive population alongside the recursive one"
    );
    // Sorted: collected from a BTreeMap, but the table is the claim.
    flagged.sort();
    assert_eq!(
        flagged, RECURSIVE_INDUCTIVES,
        "the recursive inductives at the pin; a new one is a real change in the artifact"
    );
}

/// Every level parameter a level mentions.
fn level_parameters(level: &fln_core::level::Level, out: &mut BTreeSet<String>) {
    let mut stack = vec![level];
    while let Some(current) = stack.pop() {
        match current.view() {
            LevelView::Param(name) => drop(out.insert(name.to_display_string())),
            LevelView::Succ(inner) => stack.push(inner),
            LevelView::Max(a, b) | LevelView::IMax(a, b) => {
                stack.push(a);
                stack.push(b);
            }
            LevelView::Zero | LevelView::MVar(_) => {}
        }
    }
}

/// Every level parameter an expression mentions, through both carriers: a
/// `Sort`'s level and a `Const`'s level arguments.
fn used_level_parameters(root: &Expr) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut seen: BTreeSet<usize> = BTreeSet::new();
    let mut stack: Vec<&Expr> = vec![root];
    while let Some(current) = stack.pop() {
        if !seen.insert(current.allocation_identity()) {
            continue;
        }
        match current.node() {
            ExprNode::Sort { level } => level_parameters(level, &mut out),
            ExprNode::Const { levels, .. } => {
                for level in levels {
                    level_parameters(level, &mut out);
                }
            }
            ExprNode::App { f, a } => {
                stack.push(f);
                stack.push(a);
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                stack.push(binder_type);
                stack.push(body);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                stack.push(type_);
                stack.push(value);
                stack.push(body);
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => stack.push(expr),
            ExprNode::BVar { .. } | ExprNode::FVar { .. } | ExprNode::MVar { .. } => {}
            ExprNode::Lit { .. } => {}
        }
    }
    out
}

/// The universe half of name resolution — `level_params` read as NAMES rather
/// than as the count the arity cell reads.
///
/// Two reject classes live here and neither is touched anywhere else in this
/// file: `UndefinedLevelParam` (KR-140) for a universe parameter used but not
/// declared, and `DuplicateLevelParams` (KR-971) for a declaration listing one
/// twice. Both are properties of a decoded declaration against ITSELF, so they
/// survive every closure and block check above being green.
///
/// Measured over `Init/Prelude` at private level: 2,314 declarations, 1,592
/// level-polymorphic with up to 7 parameters and 11 distinct names in use; zero
/// duplicate parameter lists; zero parameters used without being declared.
///
/// A third fact falls out and is asserted because it is stronger than either:
/// the count of declarations DECLARING a parameter equals the count USING one.
/// Since nothing uses an undeclared parameter, users are a subset of declarers,
/// so equal counts make the two sets identical — no declaration at the pin
/// carries a level parameter it never mentions.
#[test]
fn level_parameters_are_declared_distinct_and_all_of_them_are_used() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut declaring = 0usize;
    let mut using = 0usize;
    let mut widest = 0usize;
    let mut names_in_use: BTreeSet<String> = BTreeSet::new();
    for info in &infos {
        let name = info.name().to_display_string();
        let declared_list = &info.constant_val().level_params;
        let declared: BTreeSet<String> =
            declared_list.iter().map(Name::to_display_string).collect();
        assert_eq!(
            declared.len(),
            declared_list.len(),
            "{name} lists a level parameter twice, which is KR-971"
        );
        if !declared.is_empty() {
            declaring += 1;
            widest = widest.max(declared.len());
        }

        let mut used = used_level_parameters(&info.constant_val().type_);
        for expr in declaration_expressions(info) {
            used.append(&mut used_level_parameters(expr));
        }
        let undeclared: Vec<&String> = used.difference(&declared).collect();
        assert!(
            undeclared.is_empty(),
            "{name} uses level parameters it does not declare, which is KR-140: {undeclared:?}"
        );
        if !used.is_empty() {
            using += 1;
            names_in_use.extend(used);
        }
    }

    // Anti-vacuity on both sides. A level walk that found nothing would report
    // zero undeclared parameters for every declaration in the corpus, and a
    // corpus with no polymorphism would make the comparison empty.
    assert!(
        declaring > 1_500 && using > 1_500 && widest >= 7 && names_in_use.len() >= 10,
        "the pin is heavily level-polymorphic ({declaring} declaring, {using} using, widest \
         {widest}, {} distinct names)",
        names_in_use.len()
    );
    assert_eq!(
        declaring, using,
        "every declaration carrying level parameters must actually use one: nothing uses an \
         undeclared parameter, so equal counts make these the same set, and a gap would mean \
         the pin declares universes it never mentions"
    );
}

/// The axioms `Init/Prelude` retains, split by the `is_unsafe` byte.
///
/// This is the one decoded field in the file with an INDEPENDENT source of
/// truth: each of these is declared in `vendor/lean4-src/src/Init/Prelude.lean`,
/// and the keyword there says which. `unsafe axiom` for the compiler
/// primitives, plain `axiom` for the two real ones — `Classical.choice` at the
/// bottom of the `Nonempty` section and `sorryAx` beside the `sorry` support.
/// Every other cell here checks the artifact against itself; this one checks it
/// against the source the artifact was built from.
///
/// Hand-listed rather than derived from the `.lean` text, deliberately. The
/// declarations are inconsistently qualified — `unsafe axiom Quot.lcInv` and
/// `axiom Classical.choice` are written out in full while `lcProof` and
/// `isScalarObj` are namespace-relative — so a text rule would need exactly the
/// name-shape reasoning that has silently under-covered three times in this
/// file. Ten names read at their declaration sites is the safer form, and the
/// split is what makes it non-vacuous: an all-false decode fails on the eight,
/// an all-true decode fails on the two.
const UNSAFE_PRELUDE_AXIOMS: &[&str] = &[
    "Quot.lcInv",
    "isScalarObj",
    "lcAny",
    "lcCast",
    "lcErased",
    "lcProof",
    "lcUnreachable",
    "lcVoid",
];
const SAFE_PRELUDE_AXIOMS: &[&str] = &["Classical.choice", "sorryAx"];

/// `is_unsafe` on axioms and opaques — the last stored fields nothing reads.
///
/// KR-973 refuses a safe context that references an unsafe declaration, so this
/// byte decides whether a whole class of references is admissible. A decode that
/// cleared it would make the compiler primitives look like ordinary axioms and
/// quietly widen what a safe declaration may mention; a decode that set it would
/// make `Classical.choice` unusable from safe code.
///
/// Measured over `Init/Prelude` at private level: 10 axioms, 8 unsafe and 2
/// safe, matching the vendored declarations; and 14 opaques, of which 2 are
/// unsafe.
#[test]
fn the_unsafe_byte_on_axioms_and_opaques_matches_the_vendored_declarations() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut unsafe_axioms: Vec<String> = Vec::new();
    let mut safe_axioms: Vec<String> = Vec::new();
    let mut opaques = 0usize;
    let mut unsafe_opaques = 0usize;
    for info in &infos {
        let name = info.name().to_display_string();
        match info {
            ConstantInfo::Axiom(v) => {
                if v.is_unsafe {
                    unsafe_axioms.push(name);
                } else {
                    safe_axioms.push(name);
                }
            }
            ConstantInfo::Opaque(v) => {
                opaques += 1;
                if v.is_unsafe {
                    unsafe_opaques += 1;
                }
            }
            _ => {}
        }
    }

    // Sorted: collected in the module's constant order, but the table is the
    // claim rather than the order.
    unsafe_axioms.sort();
    safe_axioms.sort();
    assert_eq!(
        unsafe_axioms, UNSAFE_PRELUDE_AXIOMS,
        "the compiler primitives are `unsafe axiom` in the vendored source; a decode that \
         cleared this byte would let safe declarations reference them"
    );
    assert_eq!(
        safe_axioms, SAFE_PRELUDE_AXIOMS,
        "`Classical.choice` and `sorryAx` are plain `axiom` in the vendored source; a decode \
         that set this byte would make them unusable from safe code"
    );

    // The opaque half. Both populations are required to be real for the same
    // reason as above: a uniform byte satisfies one side and fails the other
    // only if the other side exists.
    assert!(
        opaques >= 10 && unsafe_opaques >= 1 && unsafe_opaques < opaques,
        "the pin carries both safe and unsafe opaques ({unsafe_opaques} unsafe of {opaques})"
    );
}

/// The reflexive inductives, and the modules that hold them.
///
/// Four across the 600 `Init` modules carrying a complete chain. `Init/Prelude`
/// has NONE, which is why the previous increment declined to bind this flag
/// there — an assertion over a module where every value is false is a green
/// with no evidence behind it.
const REFLEXIVE_INDUCTIVES: &[(&str, &[&str])] = &[
    ("Init/WF", &["Acc", "Acc.below"]),
    (
        "Init/Internal/Order/Basic",
        &["Lean.Order.iterates", "Lean.Order.iterates.below"],
    ),
];

/// `is_reflexive`, bound where it is actually true — and `Acc` in particular,
/// because this bead runs on it.
///
/// Comment 2250 recorded this flag as deliberately unasserted: every inductive
/// in `Init/Prelude` carries it false, so any check there would be a vacuous
/// zero. That was a disclosed gap, and a disclosed gap is worth nothing until
/// the thing it names is run. Searching the 600 `Init` modules finds exactly
/// four reflexive inductives, and the first of them is `Acc`.
///
/// `Acc` is the type the whole bead runs on: it is one of the 76 subsingletons
/// whose large elimination the 228 rows were about, and the theorem-unfold
/// repair at `e7cdcbbc` turns on its shape. So this cell also pins the four
/// observables that argument needs, on the artifact rather than in a comment:
///
///   `Acc` is reflexive, is recursive, has ONE constructor, and that
///   constructor has FIELDS — therefore `Acc.rec` carries `k = false`, and K
///   conversion cannot stand in for reducing a theorem major premise.
///
/// The K-population cell pins `k = true` for exactly `Eq`, `HEq` and `True` in
/// `Prelude` with `PUnit` as the negative control. `Acc` is the other half of
/// that control from a different module: a Prop with a single constructor, which
/// still does not get K, because its constructor is not field-free.
///
/// Non-vacuity comes from the contrast rather than a floor: a decode returning
/// `false` everywhere fails on `Init/WF`, and one returning `true` everywhere
/// fails on `Init/Prelude`.
#[test]
fn the_reflexive_flag_is_bound_where_it_is_true_and_acc_still_refuses_k() {
    let lib = lib_or_skip!();

    for (module, expected) in REFLEXIVE_INDUCTIVES {
        let (infos, _) = decode_at(&lib, &module.replace('/', "."), Level::Private);
        let mut reflexive: Vec<String> = infos
            .iter()
            .filter_map(|info| match info {
                ConstantInfo::Induct(v) if v.is_reflexive => Some(info.name().to_display_string()),
                _ => None,
            })
            .collect();
        // Sorted: the table is the claim, not the constant array's order.
        reflexive.sort();
        assert_eq!(
            reflexive, *expected,
            "{module}: the reflexive inductives at the pin"
        );
    }

    // The contrast that makes the above non-vacuous, and the reason this flag
    // could not be bound in the previous increment.
    let prelude = decode_prelude_private(&lib);
    assert!(
        !prelude
            .iter()
            .any(|info| matches!(info, ConstantInfo::Induct(v) if v.is_reflexive)),
        "Init/Prelude carries no reflexive inductive; if that changes, the flag can and should \
         be bound there too"
    );

    // `Acc`, and the four observables the `e7cdcbbc` reachability argument uses.
    let (wf, _) = decode_at(&lib, "Init.WF", Level::Private);
    let find = |name: &str| {
        wf.iter()
            .find(|info| info.name().to_display_string() == name)
            .unwrap_or_else(|| panic!("{name} decodes from Init/WF"))
    };
    let ConstantInfo::Induct(acc) = find("Acc") else {
        panic!("Acc is an inductive")
    };
    assert!(
        acc.is_reflexive && acc.is_rec,
        "Acc is reflexive and recursive"
    );
    assert_eq!(acc.ctors.len(), 1, "Acc has a single constructor");
    let ConstantInfo::Ctor(intro) = find("Acc.intro") else {
        panic!("Acc.intro is a constructor")
    };
    assert!(
        intro.num_fields > 0,
        "Acc.intro must carry fields — a field-free single constructor is what earns K"
    );
    let ConstantInfo::Rec(acc_rec) = find("Acc.rec") else {
        panic!("Acc.rec is a recursor")
    };
    assert!(
        !acc_rec.k,
        "Acc.rec must NOT carry K. This is the observable the theorem-unfold repair depends on: \
         a Prop whose recursor eliminates into data, whose constructor has fields, so neither \
         proof irrelevance nor K conversion can substitute for reducing a theorem major."
    );
}

/// `num_nested` — the field that LICENSES two carve-outs in this file, and was
/// itself never asserted.
///
/// `NESTED_AUXILIARY_RECURSORS` and `NESTED_NUMERIC_EXCEPTIONS` both excuse
/// `Lean.Syntax` recursors from an equality, and both justify it the same way:
/// the block is nested. Each cell checks that its own exceptions have
/// `num_nested > 0` — but neither bounds how many nested blocks EXIST. If a
/// second one appeared, its recursors would be excused by exactly the same
/// clause, and a genuine defect there would read as more of the same nesting.
/// A carve-out whose population is unbounded is not a carve-out, it is a hole.
///
/// This closes it for the module both cells measure: `Init/Prelude` has exactly
/// ONE nested inductive, `Lean.Syntax` at depth 2, and all three excused
/// recursors name that one block. So the exceptions are not a class the artifact
/// could quietly grow — they are three recursors of a single known block.
///
/// The wider measurement, recorded as provenance rather than paid for here: a
/// scan of all 600 `Init` modules carrying a complete chain finds `num_nested`
/// nonzero for that same single inductive and no other. Asserting that would
/// mean decoding roughly 65,000 declarations for one integer, which is not worth
/// the runtime; asserting it over the module the carve-outs live in is.
const NESTED_BLOCK: (&str, u32) = ("Lean.Syntax", 2);

#[test]
fn exactly_one_nested_block_licenses_every_nesting_carve_out_in_this_file() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut nested: Vec<(String, u32)> = Vec::new();
    let mut recursor_blocks: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut inductives = 0usize;
    for info in &infos {
        let name = info.name().to_display_string();
        match info {
            ConstantInfo::Induct(v) => {
                inductives += 1;
                if v.num_nested > 0 {
                    nested.push((name, v.num_nested));
                }
            }
            ConstantInfo::Rec(v) => {
                recursor_blocks.insert(name, v.all.iter().map(Name::to_display_string).collect());
            }
            _ => {}
        }
    }

    // Anti-vacuity: the scan must actually reach a large inductive population,
    // or "exactly one nested" is satisfied by having seen almost nothing.
    assert!(
        inductives > 100,
        "expected the pin's inductive census, got {inductives}"
    );
    assert_eq!(
        nested,
        vec![(NESTED_BLOCK.0.to_string(), NESTED_BLOCK.1)],
        "a SECOND nested block would be excused by the same clause that excuses Lean.Syntax in \
         the rules and numeric-observable cells, so its arrival must fail here rather than be \
         absorbed there"
    );

    // Every recursor either carve-out excuses must belong to that one block.
    for recursor in NESTED_AUXILIARY_RECURSORS
        .iter()
        .chain(NESTED_NUMERIC_EXCEPTIONS)
    {
        let block = recursor_blocks
            .get(*recursor)
            .unwrap_or_else(|| panic!("{recursor} must decode as a recursor"));
        assert_eq!(
            block,
            &vec![NESTED_BLOCK.0.to_string()],
            "{recursor} is excused as nesting, so it must name the one nested block"
        );
    }
}

/// The opaques that exist only at private level, and they are this bead's own
/// family: the `.loop` auxiliaries named in its filing text alongside `match_N`
/// and `_proof_N`.
const PRIVATE_ONLY_OPAQUES: &[&str] = &[
    "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop",
    "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop",
];

/// `OpaqueVal.value` — the last stored field in a `ConstantInfo` that nothing
/// asserts about.
///
/// The closure and hints cells WALK it, because `declaration_expressions`
/// includes it, but no cell says anything about what is in it. That gap matters
/// because an opaque is the one kind whose body is checked and then never used:
/// admission type-checks the value against the declared type under KR-974,
/// while the delta gate refuses to unfold it — the explicit `Opaque` arm added
/// at `ccc44fe6`. A decode that produced a placeholder body would satisfy every
/// reference and resolution check in this file and would only ever be caught by
/// the kernel actually checking it.
///
/// Measured over `Init/Prelude` at private level: 14 opaques, every one with a
/// real body — 3 to 11 distinct constants across 5 to 36 nodes, no empty or
/// trivial value among them.
///
/// The exported comparison splits them, and the split is the interesting half:
///
///   12 are `Axiom` at exported level — the body was withheld, then restored
///    2 are ABSENT from the exported part entirely
///
/// Those two are `getHeadInfo?.loop` and `getTailPos?.loop`, the `.loop` members
/// of the auxiliary family this bead's filing text named. Their `.match_1`
/// siblings are two of the six `ArtifactIncomplete` rows pinned above, so the
/// same declaration family shows up here in a third shape: absent at exported
/// level, opaque with a real body at private level.
#[test]
fn every_opaque_carries_a_real_body_and_two_of_them_exist_only_privately() {
    let lib = lib_or_skip!();
    let private = decode_prelude_private(&lib);
    let (exported, _) = decode_at(&lib, "Init.Prelude", Level::Exported);
    let exported_kinds: BTreeMap<String, &'static str> = exported
        .iter()
        .map(|info| (info.name().to_display_string(), kind_of(info)))
        .collect();

    let mut private_only: Vec<String> = Vec::new();
    let mut restored_from_axiom = 0usize;
    let mut smallest_body = usize::MAX;
    let mut opaques = 0usize;
    for info in &private {
        let ConstantInfo::Opaque(v) = info else {
            continue;
        };
        let name = info.name().to_display_string();
        opaques += 1;

        // A placeholder body would pass every other cell in this file.
        let referenced = referenced_constants(&v.value);
        assert!(
            !referenced.is_empty(),
            "{name}: an opaque's value is type-checked at admission, so a body referencing \
             nothing at all is not a body"
        );
        smallest_body = smallest_body.min(referenced.len());

        match exported_kinds.get(&name).copied() {
            Some("Axiom") => restored_from_axiom += 1,
            None => private_only.push(name),
            other => panic!("{name}: unexpected exported kind {other:?} for an opaque"),
        }
    }

    assert!(
        opaques >= 10 && smallest_body >= 2,
        "the pin's opaques must be a real population with real bodies ({opaques} opaques, \
         smallest body references {smallest_body} constants)"
    );
    assert!(
        restored_from_axiom >= 10,
        "most opaques are postulated at exported level and restored by the private part, got \
         {restored_from_axiom}"
    );
    // Sorted: the table is the claim, not the constant array's order.
    private_only.sort();
    assert_eq!(
        private_only, PRIVATE_ONLY_OPAQUES,
        "the opaques with no exported counterpart are the `.loop` auxiliaries this bead named; \
         a new one is a new member of that family and should be adjudicated, not absorbed"
    );
}

/// The `Expr` payloads every walker in this file steps over.
///
/// The field inventory I called complete at comment 2264 was over
/// `ConstantInfo`. Inside an `Expr` there are stored payloads that every walker
/// here explicitly skips: a projection's `struct_name` and `idx`, a binder's
/// `BinderInfo`, a literal's value, `MData`'s map. They are decoded, they are
/// never read back, and two of them carry a checkable relation.
///
/// PROJECTIONS. `Expr::proj` is reduced by the kernel — the matching-projection
/// pre-pass and `finish_infer_proj` both dispatch on it — so a wrong
/// `struct_name` or an out-of-range `idx` changes reduction rather than failing
/// to decode. The relation: `struct_name` must be a decoded inductive with
/// exactly ONE constructor, and `idx` must be below that constructor's
/// `num_fields`. Measured over `Init/Prelude` at private level: 207 projection
/// nodes over roughly 100 distinct structures, indices 0 through 5, zero
/// violations.
///
/// BINDER INFO. Not a relation but a census, and a census is what it needs:
/// every binder carries one, they are 20,064 `Default`, 8,618 `Implicit` and
/// 497 `InstImplicit`, and a decode collapsing them to a single value would
/// change every regenerated recursor type — a `BlockMismatch` with every name
/// and count in this file still agreeing. Requiring all three to appear is what
/// makes that collapse fail here.
#[test]
fn projection_targets_resolve_and_binder_info_is_not_collapsed() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut single_ctor_fields: BTreeMap<String, u32> = BTreeMap::new();
    let mut constructors: BTreeMap<String, &ConstructorVal> = BTreeMap::new();
    for info in &infos {
        if let ConstantInfo::Ctor(v) = info {
            constructors.insert(info.name().to_display_string(), v);
        }
    }
    for info in &infos {
        if let ConstantInfo::Induct(v) = info
            && v.ctors.len() == 1
            && let Some(ctor) = constructors.get(&v.ctors[0].to_display_string())
        {
            single_ctor_fields.insert(info.name().to_display_string(), ctor.num_fields);
        }
    }

    let mut projections = 0usize;
    let mut widest_index = 0u64;
    let mut binders: BTreeMap<&'static str, usize> = BTreeMap::new();
    for info in &infos {
        for root in declaration_expressions(info) {
            let mut seen: BTreeSet<usize> = BTreeSet::new();
            let mut stack: Vec<&Expr> = vec![root];
            while let Some(current) = stack.pop() {
                if !seen.insert(current.allocation_identity()) {
                    continue;
                }
                match current.node() {
                    ExprNode::Proj {
                        struct_name,
                        idx,
                        expr,
                    } => {
                        projections += 1;
                        widest_index = widest_index.max(*idx);
                        let name = struct_name.to_display_string();
                        let fields = single_ctor_fields.get(&name).unwrap_or_else(|| {
                            panic!(
                                "projection on `{name}`, which is not a decoded \
                                 single-constructor inductive"
                            )
                        });
                        assert!(
                            *idx < u64::from(*fields),
                            "projection {name}.{idx} is past its constructor's {fields} fields"
                        );
                        stack.push(expr);
                    }
                    ExprNode::Lam { binder_info, .. } | ExprNode::ForallE { binder_info, .. } => {
                        *binders.entry(binder_info_name(*binder_info)).or_default() += 1;
                        if let ExprNode::Lam {
                            binder_type, body, ..
                        }
                        | ExprNode::ForallE {
                            binder_type, body, ..
                        } = current.node()
                        {
                            stack.push(binder_type);
                            stack.push(body);
                        }
                    }
                    ExprNode::App { f, a } => {
                        stack.push(f);
                        stack.push(a);
                    }
                    ExprNode::LetE {
                        type_, value, body, ..
                    } => {
                        stack.push(type_);
                        stack.push(value);
                        stack.push(body);
                    }
                    ExprNode::MData { expr, .. } => stack.push(expr),
                    ExprNode::BVar { .. }
                    | ExprNode::FVar { .. }
                    | ExprNode::MVar { .. }
                    | ExprNode::Sort { .. }
                    | ExprNode::Const { .. }
                    | ExprNode::Lit { .. } => {}
                }
            }
        }
    }

    assert!(
        projections >= 150 && widest_index >= 4,
        "projections must be a real population reaching past index 0 ({projections} nodes, \
         widest index {widest_index})"
    );
    assert!(
        binders.len() == 3
            && binders.values().all(|count| *count > 400)
            && binders["Default"] > 10_000,
        "all three binder kinds the pin uses must survive decode: {binders:?}"
    );
}

fn binder_info_name(info: BinderInfo) -> &'static str {
    match info {
        BinderInfo::Default => "Default",
        BinderInfo::Implicit => "Implicit",
        BinderInfo::StrictImplicit => "StrictImplicit",
        BinderInfo::InstImplicit => "InstImplicit",
    }
}

/// Read one module's `ModuleData` header at the requested level.
fn module_view(lib: &Path, module: &str, level: Level) -> ModuleDataView {
    let base = lib.join(format!("{}.olean", module.replace('.', "/")));
    let read = |p: PathBuf| std::fs::read(&p).unwrap_or_else(|e| panic!("read {p:?}: {e}"));
    let exported = read(base.clone());
    match level {
        Level::Exported => OleanView::parse(&exported)
            .expect("parse exported part")
            .module_data(WalkBudget::default())
            .expect("exported module data"),
        Level::Private => {
            let server = read(base.with_extension("olean.server"));
            let private = read(base.with_extension("olean.private"));
            OleanView::parse_with_dependencies(&private, &[&exported, &server])
                .expect("parse private part")
                .module_data(WalkBudget::default())
                .expect("private module data")
        }
    }
}

/// `is_module` and the `Import` flags — module-level stored fields, outside both
/// the `ConstantInfo` and `Expr` inventories, and the missing WHY under the
/// cross-module cell.
///
/// `a435ccb4` showed that `Init.Meta.Defs` references
/// `_private.Init.Prelude.0.Lean.Name.beq.match_1` and that the reference
/// resolves only when `Init.Prelude` is read at private level. It never showed
/// what LICENSES that. An ordinary `import` gives you the exported part; `import
/// all` gives you the private one. The artifact says which, in a stored flag
/// nothing here reads.
///
/// Measured: `Init.Meta.Defs` has 7 imports and exactly ONE carries
/// `import_all` — `Init.Prelude`, the module that owns the auxiliary. So the
/// cross-module resolution that bead observed is not an accident of how the
/// replay happens to build its environment; the artifact declares the import
/// that permits it.
///
/// Two more facts fall out of the same header. `is_module` is true at BOTH
/// levels for both modules, which is the premise of the entire companion-chain
/// repair — a non-module olean has no `.private` part to read. And
/// `Init.Prelude` declares ZERO imports, which is the premise the import-free
/// closure cell rests on and had until now simply assumed.
///
/// Non-vacuity: all three import flags occur in this one header — one
/// `import_all`, two `is_exported`, one `is_meta` — so a decode returning a
/// uniform value for any of them fails here.
#[test]
fn the_import_that_licenses_the_cross_module_private_reference_is_declared() {
    let lib = lib_or_skip!();

    for level in [Level::Exported, Level::Private] {
        // The companion-chain premise: without this, there is no private part.
        assert!(
            module_view(&lib, "Init.Prelude", level).is_module,
            "Init.Prelude must be a module-system olean"
        );
        let defs = module_view(&lib, "Init.Meta.Defs", level);
        assert!(
            defs.is_module,
            "Init.Meta.Defs must be a module-system olean"
        );

        // The premise the import-free closure cell rests on.
        assert!(
            module_view(&lib, "Init.Prelude", level).imports.is_empty(),
            "Init.Prelude must import nothing; the closure cell's whole argument is that every \
             constant it references has to be declared by it"
        );

        assert!(
            defs.imports.len() >= 7,
            "Init.Meta.Defs is supposed to carry at least the 7 imports measured at the pin, \
             got {}",
            defs.imports.len()
        );
        let import_all: Vec<String> = defs
            .imports
            .iter()
            .filter(|import| import.import_all)
            .map(|import| import.module.to_display_string())
            .collect();
        assert_eq!(
            import_all,
            vec!["Init.Prelude".to_string()],
            "exactly one import may be `import all`, and it must be the module that owns the \
             private auxiliary the cross-module cell resolves"
        );

        // All three flags must be exercised, or a uniform decode passes above.
        assert!(
            defs.imports.iter().filter(|i| i.is_exported).count() >= 2
                && defs.imports.iter().any(|i| i.is_meta)
                && defs.imports.iter().any(|i| !i.is_exported && !i.is_meta),
            "the pin's import header exercises every flag; a uniform decode would not"
        );
    }
}

/// The extension blocks the private part adds and the exported part lacks.
const PRIVATE_ONLY_EXTENSIONS: &[&str] = &[
    "Lean.Compiler.LCNF.UnreachableBranches.functionSummariesExt",
    "Lean.declRangeExt",
    "Lean.docStringExt",
    "_private.Lean.Compiler.LCNF.Specialize.0.Lean.Compiler.LCNF.Specialize.specCacheExt",
    "_private.Lean.DocString.Extension.0.Lean.inheritDocStringExt",
    "_private.Lean.DocString.Extension.0.Lean.moduleDocExt",
];

/// `extraConstNames` and `entries` — the two module-header arrays left, and the
/// first of them is a hypothesis this bead already ruled out.
///
/// `extraConstNames` was investigated as a candidate source of the missing
/// equation-compiler auxiliaries and rejected: it holds IR / code-generator
/// names with no `ConstantInfo` behind them, so nothing there could ever have
/// become a declaration. The pipeline decodes it to a COUNT and never reads its
/// contents. Pinning the count is what stops that ruled-out hypothesis being
/// re-chased on the grounds that "nobody checked".
///
/// Measured over `Init/Prelude`: 424 extra names at exported level and 713 at
/// private, against 2,204 and 2,314 declarations. Both arrays GROW between the
/// levels, and they are different arrays of different sizes — the auxiliaries
/// the earlier cells recovered by name came from `constants`, not from here.
///
/// The mirror law is asserted from the header rather than from the decoder. A
/// module stores `constNames` and `constants` as two separate arrays, and
/// `decode_module_constants` enforces `constNames[i] == constants[i].name`
/// while walking them; reading the two LENGTHS off the header is an independent
/// check of the same law, one that does not go through the code enforcing it.
///
/// `entries` carries the environment extensions, and the private part is a
/// strict SUPERSET: 56 blocks exported, 62 private, nothing lost, and the six
/// additions are the documentation and compiler-cache extensions above. That is
/// the same shape as every other exported/private result on this bead — the
/// private level adds, and never removes.
#[test]
fn the_module_header_arrays_grow_between_levels_and_never_shrink() {
    let lib = lib_or_skip!();

    for module in ["Init.Prelude", "Init.Meta.Defs"] {
        let exported = module_view(&lib, module, Level::Exported);
        let private = module_view(&lib, module, Level::Private);

        for (label, view) in [("exported", &exported), ("private", &private)] {
            // The mirror law, read off the header's two array lengths.
            assert_eq!(
                view.const_names.len() as u64,
                view.constants,
                "{module} [{label}]: constNames and constants must be the same length"
            );
            assert!(
                view.extra_const_names > 0,
                "{module} [{label}]: extraConstNames is populated at the pin; a zero here would \
                 make the ruled-out hypothesis untestable rather than ruled out"
            );
            assert_ne!(
                view.extra_const_names, view.constants,
                "{module} [{label}]: extraConstNames is a DIFFERENT population from constants — \
                 the recovered auxiliaries came from the latter"
            );
        }

        assert!(
            private.constants > exported.constants
                && private.extra_const_names > exported.extra_const_names,
            "{module}: both header arrays grow between the levels (constants {} -> {}, extra {} \
             -> {})",
            exported.constants,
            private.constants,
            exported.extra_const_names,
            private.extra_const_names
        );
    }

    // Extensions: the private part adds and never removes.
    let exported = module_view(&lib, "Init.Prelude", Level::Exported);
    let private = module_view(&lib, "Init.Prelude", Level::Private);
    let exported_names: BTreeSet<&str> = exported
        .extensions
        .iter()
        .map(|block| block.name.as_str())
        .collect();
    let private_names: BTreeSet<&str> = private
        .extensions
        .iter()
        .map(|block| block.name.as_str())
        .collect();
    assert!(
        exported_names.len() >= 50 && !exported_names.is_empty(),
        "the pin carries a real extension surface, got {}",
        exported_names.len()
    );
    let lost: Vec<&&str> = exported_names.difference(&private_names).collect();
    assert!(
        lost.is_empty(),
        "the private part must not drop an extension the exported part carries: {lost:?}"
    );
    let added: Vec<&str> = private_names.difference(&exported_names).copied().collect();
    assert_eq!(
        added, PRIVATE_ONLY_EXTENSIONS,
        "the extensions only the private level carries"
    );
}

/// Count the leading `∀` binders of a type.
fn telescope_length(type_: &Expr) -> usize {
    let mut current = type_;
    let mut length = 0usize;
    while let ExprNode::ForallE { body, .. } = current.node() {
        length += 1;
        current = body;
    }
    length
}

/// The stored arities checked against the TYPE they describe.
///
/// `cd572cac` compared a recursor's `num_motives` and `num_minors` against its
/// BLOCK, and `db2ea8b0` compared a rule's `nfields` against its constructor.
/// Neither compared any of these numbers against the thing they are arities OF.
/// A constructor's `num_params` and `num_fields` describe its own type's binder
/// telescope; a recursor's four counts plus its major premise describe its own.
/// Both are derivable from the decoded type, and a decode that read a count
/// correctly but the type wrongly — or the reverse — passes every earlier cell.
///
/// Measured over `Init/Prelude` at private level: 157 constructors, every
/// telescope exactly `num_params + num_fields`; 129 recursors, every telescope
/// exactly `num_params + num_motives + num_minors + num_indices + 1`.
///
/// THE RECURSOR RESULT NARROWS AN EARLIER CARVE-OUT, which is the part worth
/// keeping. The three `Lean.Syntax` recursors are excused in two other cells
/// because their motive and minor counts describe the nested-EXPANDED block
/// rather than their `all` list. They need no exception here: their stored
/// counts match their own type exactly. So those recursors are internally
/// consistent, and the exception is to a block-derived expectation rather than
/// to anything about the recursors themselves — a narrower claim than "nested
/// recursors are different", and the accurate one.
#[test]
fn stored_arities_match_the_telescopes_they_describe() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut constructors = 0usize;
    let mut with_fields = 0usize;
    let mut recursors = 0usize;
    for info in &infos {
        let name = info.name().to_display_string();
        match info {
            ConstantInfo::Ctor(v) => {
                constructors += 1;
                if v.num_fields > 0 {
                    with_fields += 1;
                }
                assert_eq!(
                    telescope_length(&v.base.type_),
                    (v.num_params + v.num_fields) as usize,
                    "{name}: type telescope must be exactly its parameters plus its fields"
                );
            }
            ConstantInfo::Rec(v) => {
                recursors += 1;
                // Parameters, motives, minor premises, indices, then the major.
                let expected =
                    (v.num_params + v.num_motives + v.num_minors + v.num_indices) as usize + 1;
                assert_eq!(
                    telescope_length(&v.base.type_),
                    expected,
                    "{name}: type telescope must be its four counts plus the major premise. \
                     Note this needs no nesting exception — the Lean.Syntax recursors are \
                     internally consistent, and the carve-outs elsewhere are against a \
                     BLOCK-derived expectation, not against their own type."
                );
            }
            _ => {}
        }
    }

    // Anti-vacuity: an all-zero read of num_fields would satisfy the
    // constructor equality for every nullary constructor, which is 16 of 157
    // here — so the field-bearing majority has to be real.
    assert!(
        constructors >= 150 && with_fields >= 130 && recursors >= 120,
        "the pin's block census must be reached ({constructors} constructors, {with_fields} \
         with fields, {recursors} recursors)"
    );
}

/// A constructor's result type: what it is headed by, and how many arguments it
/// applies.
///
/// The arity cell counted the constructor's binders. It said nothing about what
/// the type RESULTS in, and that is the half the kernel actually adjudicates:
/// `crates/fln-kernel/tests/large_elimination_imax.rs` carries
/// `constructor_with_foreign_result_type_is_rejected`, so a constructor whose
/// result is headed by the wrong inductive is a rejection the kernel already
/// knows how to produce. Nothing on the decode side checked that the artifact
/// never hands it one.
///
/// Two relations, both derived from the decoded type rather than from a table:
///
///   the result's HEAD must be the constructor's own `induct`
///   the result's ARGUMENT COUNT must be that inductive's
///   `num_params + num_indices`
///
/// Measured over `Init/Prelude` at private level: 157 constructors, zero
/// violations of either.
///
/// The second relation is why the first is not enough on its own. A result
/// headed correctly but applied to the wrong number of arguments is a different
/// defect — it would make the regenerated recursor's motive telescope disagree —
/// and the head check alone cannot see it. Its non-vacuity comes from the
/// indexed inductives: `Eq`, `HEq`, `Nat.le` and `Nat.le.below` carry indices at
/// this pin, so the count is not merely `num_params` for everything.
#[test]
fn constructor_results_are_headed_by_their_own_inductive_at_the_right_arity() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut inductives: BTreeMap<String, &InductiveVal> = BTreeMap::new();
    for info in &infos {
        if let ConstantInfo::Induct(v) = info {
            inductives.insert(info.name().to_display_string(), v);
        }
    }
    let indexed = inductives.values().filter(|v| v.num_indices > 0).count();
    assert!(
        indexed >= 4,
        "the pin carries indexed inductives, without which the argument count below is just \
         num_params: got {indexed}"
    );

    let mut checked = 0usize;
    for info in &infos {
        let ConstantInfo::Ctor(ctor) = info else {
            continue;
        };
        let name = info.name().to_display_string();
        let induct_name = ctor.induct.to_display_string();
        let induct = inductives
            .get(&induct_name)
            .expect("constructor's inductive decodes");

        // Strip the telescope, then walk the application spine of the result.
        let mut current = &ctor.base.type_;
        while let ExprNode::ForallE { body, .. } = current.node() {
            current = body;
        }
        let mut arguments = 0usize;
        while let ExprNode::App { f, .. } = current.node() {
            arguments += 1;
            current = f;
        }
        let ExprNode::Const { name: head, .. } = current.node() else {
            panic!("{name}: result type is not headed by a constant");
        };
        assert_eq!(
            head.to_display_string(),
            induct_name,
            "{name}: result is headed by a foreign inductive, which the kernel rejects"
        );
        assert_eq!(
            arguments,
            (induct.num_params + induct.num_indices) as usize,
            "{name}: result applies the wrong number of arguments; the head can be right while \
             this is wrong, and it would surface as a regenerated-recursor mismatch"
        );
        checked += 1;
    }
    assert!(
        checked >= 150,
        "the constructor census must be reached, got {checked}"
    );
}

/// Is this inductive's declared type a `Prop`?
///
/// `admit.rs` reads `result_level` from the DECLARED inductive type's sort
/// rather than inferring it, so this is the same value the elimination rules
/// consume.
fn inductive_result_is_prop(induct: &InductiveVal) -> bool {
    let mut current = &induct.base.type_;
    while let ExprNode::ForallE { body, .. } = current.node() {
        current = body;
    }
    matches!(current.node(), ExprNode::Sort { level } if level.is_zero())
}

/// The inductive's own result sort, and the K rule stated as an IMPLICATION
/// rather than a name list.
///
/// Two cells rest on this value without ever reading it. `admit.rs` takes
/// `result_level` from the declared inductive type's sort — not from inference —
/// so it is the input to the elimination rules the 228 rows were about. And
/// `cd572cac` asserts `k = true` for exactly `Eq`, `HEq` and `True` with `PUnit`
/// as a negative control, justified in prose by "PUnit is not a Prop". That
/// justification was never measured; the cell asserted the conclusion and
/// explained it in a comment.
///
/// Measured over `Init/Prelude` at private level: all 127 inductive types result
/// in a `Sort` — 74 `Succ`, 41 `Max`, 10 `Zero`, 2 `Param`, none headed by
/// anything else. The 10 Prop-valued ones include `Eq`, `HEq`, `True`, `And` and
/// `Nat.le`; `PUnit` and `Nat` are not among them.
///
/// So the K rule becomes derivable here instead of asserted: every recursor
/// carrying `k` has a block head that is Prop-valued, single-constructor, and
/// field-free — and `PUnit` satisfies two of those three while failing
/// Prop-ness, which is exactly why it has no K. The negative control is now a
/// measurement rather than a comment.
#[test]
fn inductives_result_in_sorts_and_k_follows_from_prop_ness() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut inductives: BTreeMap<String, &InductiveVal> = BTreeMap::new();
    let mut constructors: BTreeMap<String, &ConstructorVal> = BTreeMap::new();
    let mut recursors: Vec<(String, &RecursorVal)> = Vec::new();
    for info in &infos {
        let name = info.name().to_display_string();
        match info {
            ConstantInfo::Induct(v) => drop(inductives.insert(name, v)),
            ConstantInfo::Ctor(v) => drop(constructors.insert(name, v)),
            ConstantInfo::Rec(v) => recursors.push((name, v)),
            _ => {}
        }
    }

    // Every inductive type must END in a sort, or `result_level` is reading
    // something that is not a universe.
    for (name, induct) in &inductives {
        let mut current = &induct.base.type_;
        while let ExprNode::ForallE { body, .. } = current.node() {
            current = body;
        }
        assert!(
            matches!(current.node(), ExprNode::Sort { .. }),
            "{name}: an inductive's declared type must result in a Sort — that value is what \
             the elimination rules read"
        );
    }
    let props = inductives
        .values()
        .filter(|v| inductive_result_is_prop(v))
        .count();
    assert!(
        props >= 8 && props < inductives.len(),
        "both Prop and non-Prop inductives must exist, or the implication below is vacuous \
         ({props} Prop of {})",
        inductives.len()
    );

    // K implies Prop AND single constructor AND no fields.
    for (name, rec) in &recursors {
        if !rec.k {
            continue;
        }
        let head = inductives
            .get(&rec.all[0].to_display_string())
            .expect("recursor's block head decodes");
        assert!(
            inductive_result_is_prop(head),
            "{name} carries K, so its inductive must be a Prop"
        );
        assert_eq!(head.ctors.len(), 1, "{name} carries K, so one constructor");
        let ctor = constructors
            .get(&head.ctors[0].to_display_string())
            .expect("constructor decodes");
        assert_eq!(
            ctor.num_fields, 0,
            "{name} carries K, so its constructor must be field-free"
        );
    }

    // The negative control, now derived rather than asserted: PUnit meets two of
    // the three conditions and fails Prop-ness.
    let punit = inductives.get("PUnit").expect("PUnit decodes");
    assert_eq!(punit.ctors.len(), 1);
    assert_eq!(
        constructors
            .get(&punit.ctors[0].to_display_string())
            .expect("PUnit.unit decodes")
            .num_fields,
        0
    );
    assert!(
        !inductive_result_is_prop(punit),
        "PUnit is single-constructor and field-free, so Prop-ness is the ONLY thing standing \
         between it and K; if it ever measures as a Prop, the K population must grow with it"
    );
}

/// Count the leading `fun` binders of a term.
fn lambda_length(value: &Expr) -> usize {
    let mut current = value;
    let mut length = 0usize;
    while let ExprNode::Lam { body, .. } = current.node() {
        length += 1;
        current = body;
    }
    length
}

/// The iota right-hand side's own shape.
///
/// `db2ea8b0` checked which constructor each rule names and how many fields it
/// binds. Both are properties of the rule's HEADER. The `rhs` — the term the
/// recursor reduces TO — is walked by the closure cells and has never had a
/// relation asserted about it, even though it is the thing iota actually
/// produces: `reduce_recursor` substitutes into this term, so a wrong shape is a
/// wrong reduction rather than a decode failure.
///
/// The relation: a rule's `rhs` abstracts the recursor's parameters, motives and
/// minor premises, then the constructor's own fields, so its lambda telescope is
/// exactly `num_params + num_motives + num_minors + rule.nfields`.
///
/// Measured over `Init/Prelude` at private level: 160 rules, every one an exact
/// match — the deviation histogram is a single bucket at zero.
///
/// It is a genuinely discriminating length because it is not a constant: the
/// expected values span 2 to 18 across 17 distinct lengths, drawn from four
/// independently stored numbers. A decode that misread ANY of the four, or that
/// truncated a lambda spine, moves a length and fails here. That is the reason
/// to check the telescope rather than merely that the `rhs` is a lambda at all.
#[test]
fn every_iota_right_hand_side_abstracts_exactly_its_recursors_telescope() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut rules = 0usize;
    let mut lengths: BTreeSet<usize> = BTreeSet::new();
    for info in &infos {
        let ConstantInfo::Rec(rec) = info else {
            continue;
        };
        let name = info.name().to_display_string();
        for rule in &rec.rules {
            let expected =
                (rec.num_params + rec.num_motives + rec.num_minors + rule.nfields) as usize;
            assert_eq!(
                lambda_length(&rule.rhs),
                expected,
                "{name}'s rule for {}: the iota right-hand side must abstract the recursor's \
                 parameters, motives and minors, then the constructor's fields",
                rule.ctor.to_display_string()
            );
            lengths.insert(expected);
            rules += 1;
        }
    }

    // Non-vacuity: a constant expected length would make this satisfiable by a
    // decoder that got one number right and reused it everywhere.
    assert!(
        rules >= 150 && lengths.len() >= 10,
        "the expected telescope must vary across the pin's rules ({rules} rules, {} distinct \
         lengths)",
        lengths.len()
    );
    assert!(
        *lengths.iter().next_back().expect("nonempty") >= 12,
        "the pin reaches long iota telescopes; a decode truncating a lambda spine would show up \
         at the top of this range first"
    );
}

/// The `all` lists agree with each other — a relation between two fields this
/// file already reads separately.
///
/// `InductiveVal.all` and `RecursorVal.all` both name a block. Cells above use
/// each of them: the rules cell gathers a block's constructors by iterating
/// `rec.all`, the numeric cell counts motives against its length, and the
/// nesting cell keys carve-outs off `rec.all[0]`. Not one of them checks that
/// the two lists AGREE. A recursor naming a different block than its inductive
/// declares would send every one of those cells to the wrong constructor set and
/// they would all still pass, because each is internally consistent with the
/// list it happened to read.
///
/// Three coherence relations, over `Init/Prelude` at private level — 127
/// inductives, 129 recursors, 157 constructors, zero violations of any:
///
///   an inductive's `all` contains the inductive itself
///   a recursor's `all` equals its head inductive's `all`
///   a constructor's `induct` is a member of that inductive's own `all`
///
/// SCOPE, AND IT IS A LIMIT ON EVERY `all`-ITERATING CELL IN THIS FILE, NOT JUST
/// THIS ONE. A scan of all 600 `Init` modules carrying a complete chain finds
/// ZERO mutual inductive blocks: every `all` in the corpus this file measures is
/// a singleton. So these relations, and the block iteration in the cells above,
/// have only ever been exercised on one-type blocks. They are stated as laws
/// rather than as "`all` has one element" precisely so that a mutual block
/// arriving is checked rather than rejected — but nothing here has yet SEEN one,
/// and that is worth knowing before this file's block coverage is described as
/// complete.
#[test]
fn inductive_and_recursor_block_lists_agree() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut inductives: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for info in &infos {
        if let ConstantInfo::Induct(v) = info {
            inductives.insert(
                info.name().to_display_string(),
                v.all.iter().map(Name::to_display_string).collect(),
            );
        }
    }
    assert!(
        inductives.len() > 100,
        "the inductive census must be reached, got {}",
        inductives.len()
    );

    for (name, all) in &inductives {
        assert!(
            all.contains(name),
            "{name}: an inductive must be a member of its own block, or every lookup keyed on \
             `all` goes somewhere else"
        );
        for member in all {
            assert_eq!(
                inductives.get(member),
                Some(all),
                "{name}: block member {member} declares a different block"
            );
        }
    }

    let mut recursors = 0usize;
    let mut constructors = 0usize;
    for info in &infos {
        match info {
            ConstantInfo::Rec(v) => {
                recursors += 1;
                let all: Vec<String> = v.all.iter().map(Name::to_display_string).collect();
                let head = inductives
                    .get(&all[0])
                    .expect("recursor's head inductive decodes");
                assert_eq!(
                    &all,
                    head,
                    "{}: a recursor's block must be the block its head inductive declares",
                    info.name().to_display_string()
                );
            }
            ConstantInfo::Ctor(v) => {
                constructors += 1;
                let induct = v.induct.to_display_string();
                let all = inductives
                    .get(&induct)
                    .expect("constructor's inductive decodes");
                assert!(
                    all.contains(&induct),
                    "{}: its inductive is not a member of its own block",
                    info.name().to_display_string()
                );
            }
            _ => {}
        }
    }
    assert!(
        recursors > 100 && constructors > 120,
        "both populations must be reached ({recursors} recursors, {constructors} constructors)"
    );
}

/// The level-parameter relation between a block's three declarations — which is
/// the observable the 228 rows disagreed on.
///
/// d17i's `BlockMismatch` family was exactly this: the kernel regenerated a
/// recursor whose level-parameter list was one SHORTER than the decoded one,
/// reported as `generated [u,v,w]` against `decoded [u_1,u,v,w]`. The repair at
/// `50f65ba4` restored the missing motive universe. Nothing has ever checked the
/// decoded side of that comparison — what the artifact actually carries.
///
/// Measured over `Init/Prelude` at private level:
///
///   157 constructors, every one sharing its inductive's level parameters exactly
///   124 recursors carrying one EXTRA parameter, PREPENDED, over their inductive
///     5 recursors carrying exactly their inductive's, with nothing added
///
/// No recursor takes any other shape: the extra is always a single name and
/// always first, never appended or interleaved.
///
/// THE FIVE WITHOUT AN EXTRA ARE ALL PROP-BASED — they eliminate only into
/// `Prop`, so there is no motive universe to carry. But the converse fails, and
/// that is the part worth pinning: five OTHER Prop-based recursors DO carry the
/// extra parameter. Prop-ness alone does not decide whether a block gets a
/// motive universe; being a SUBSINGLETON does, which is precisely the
/// distinction `elim_only_at_universe_zero` was making structurally when it cost
/// 228 rows. The artifact says both populations exist, so a rule keyed on
/// Prop-ness alone is refutable here rather than only in the lane.
#[test]
fn recursor_level_parameters_extend_their_inductives_by_at_most_a_motive_universe() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut inductives: BTreeMap<String, &InductiveVal> = BTreeMap::new();
    for info in &infos {
        if let ConstantInfo::Induct(v) = info {
            inductives.insert(info.name().to_display_string(), v);
        }
    }
    let params = |v: &ConstantVal| -> Vec<String> {
        v.level_params.iter().map(Name::to_display_string).collect()
    };

    let mut constructors = 0usize;
    let mut extended = 0usize;
    let mut unextended = 0usize;
    let mut prop_extended = 0usize;
    let mut prop_unextended = 0usize;
    for info in &infos {
        let name = info.name().to_display_string();
        match info {
            ConstantInfo::Ctor(v) => {
                constructors += 1;
                let induct = inductives
                    .get(&v.induct.to_display_string())
                    .expect("constructor's inductive decodes");
                assert_eq!(
                    params(&v.base),
                    params(&induct.base),
                    "{name}: a constructor shares its inductive's universe parameters"
                );
            }
            ConstantInfo::Rec(v) => {
                let head = inductives
                    .get(&v.all[0].to_display_string())
                    .expect("recursor's head inductive decodes");
                let mine = params(&v.base);
                let theirs = params(&head.base);
                let is_prop = inductive_result_is_prop(head);
                if mine == theirs {
                    unextended += 1;
                    if is_prop {
                        prop_unextended += 1;
                    }
                } else {
                    assert_eq!(
                        mine.len(),
                        theirs.len() + 1,
                        "{name}: a recursor may add at most one universe over its inductive"
                    );
                    assert_eq!(
                        &mine[1..],
                        theirs.as_slice(),
                        "{name}: the motive universe is PREPENDED — `decoded [u_1,u,v,w]` is the \
                         shape the 228 rows reported against a regeneration that dropped it"
                    );
                    extended += 1;
                    if is_prop {
                        prop_extended += 1;
                    }
                }
            }
            _ => {}
        }
    }

    assert!(
        constructors > 120 && extended > 100 && unextended > 0,
        "both recursor populations must be present ({extended} extended, {unextended} not)"
    );
    // The refutation of "Prop implies no motive universe". Both Prop populations
    // must be non-empty, or that wrong rule is indistinguishable from the right
    // one over this artifact — and it is the wrong rule that cost 228 rows.
    assert!(
        prop_unextended > 0 && prop_extended > 0,
        "Prop-ness alone must NOT determine the motive universe: {prop_extended} Prop-based \
         recursors carry the extra parameter and {prop_unextended} do not"
    );
}

/// The leading `num` binder domains of a type.
fn leading_domains(type_: &Expr, num: usize) -> Vec<&Expr> {
    let mut out = Vec::new();
    let mut current = type_;
    while out.len() < num {
        let ExprNode::ForallE {
            binder_type, body, ..
        } = current.node()
        else {
            break;
        };
        out.push(binder_type);
        current = body;
    }
    out
}

/// The inductive's own arity, and the parameters it SHARES with its
/// constructors.
///
/// The arity cell checked a constructor's telescope and a recursor's. It never
/// checked the inductive's own, and the inductive is where `num_params` and
/// `num_indices` are declared — every other cell that uses those two numbers
/// takes them from here.
///
/// The second relation is the one with teeth. Block admission opens the
/// parameter telescope ONCE and reuses those locals for every constructor in the
/// block, so a constructor whose leading binders differ from its inductive's is
/// a block the kernel cannot form. Nothing checked that the artifact never
/// presents one. It is a relation between two types this file already reads
/// separately — the inductive's and the constructor's — and neither cell that
/// reads them compares them.
///
/// Measured over `Init/Prelude` at private level:
///
///   127 inductives, every telescope exactly `num_params + num_indices`
///   107 constructors of parameterised inductives, every leading parameter
///       domain equal to its inductive's; 50 more are skipped as their
///       inductive takes no parameters
///
/// Non-vacuity for the first: `num_indices` is 0 for 123 of the 127 and nonzero
/// for 4, and `num_params` ranges 0 to 6 with 28 at zero — so the sum is not a
/// constant and an equality against it is not free. For the second: the
/// parameterised majority is floored, since a check that skipped every
/// constructor would report no failures at all.
#[test]
fn inductive_arity_matches_its_type_and_constructors_share_its_parameters() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut inductives: BTreeMap<String, &InductiveVal> = BTreeMap::new();
    for info in &infos {
        if let ConstantInfo::Induct(v) = info {
            inductives.insert(info.name().to_display_string(), v);
        }
    }

    let mut indexed = 0usize;
    let mut parameterised = 0usize;
    for (name, induct) in &inductives {
        assert_eq!(
            telescope_length(&induct.base.type_),
            (induct.num_params + induct.num_indices) as usize,
            "{name}: an inductive's telescope is its parameters followed by its indices, and \
             those two numbers are what every other cell reads from here"
        );
        if induct.num_indices > 0 {
            indexed += 1;
        }
        if induct.num_params > 0 {
            parameterised += 1;
        }
    }
    assert!(
        indexed >= 4 && parameterised >= 90 && parameterised < inductives.len(),
        "the sum must not be a constant: {indexed} indexed, {parameterised} parameterised of {}",
        inductives.len()
    );

    let mut compared = 0usize;
    for info in &infos {
        let ConstantInfo::Ctor(ctor) = info else {
            continue;
        };
        let induct = inductives
            .get(&ctor.induct.to_display_string())
            .expect("constructor's inductive decodes");
        if induct.num_params == 0 {
            continue;
        }
        let count = induct.num_params as usize;
        assert_eq!(
            leading_domains(&ctor.base.type_, count),
            leading_domains(&induct.base.type_, count),
            "{}: its leading parameter binders differ from its inductive's, so block admission \
             could not open one telescope and reuse it across the block",
            info.name().to_display_string()
        );
        compared += 1;
    }
    assert!(
        compared >= 100,
        "a check that skipped every constructor would report no failures; {compared} compared"
    );
}

/// The nested auxiliary recursors and the container each one's major premise is
/// headed by.
///
/// Named with their containers rather than excluded by shape: "skip the nested
/// ones" would accept a nested recursor whose major was headed by anything at
/// all, which is the failure this relation exists to catch.
const NESTED_MAJOR_CONTAINERS: &[(&str, &str)] = &[
    ("Lean.Syntax.rec_1", "Array"),
    ("Lean.Syntax.rec_2", "List"),
];

/// Every binder domain of a type, in order.
fn all_domains(type_: &Expr) -> Vec<&Expr> {
    let mut out = Vec::new();
    let mut current = type_;
    while let ExprNode::ForallE {
        binder_type, body, ..
    } = current.node()
    {
        out.push(binder_type);
        current = body;
    }
    out
}

/// What the recursor's telescope CONTAINS, not just how long it is.
///
/// `11c4c97d` checked that a recursor's telescope has
/// `num_params + num_motives + num_minors + num_indices + 1` binders. A
/// telescope of the right length can still bind the wrong things, and two of its
/// positions are determined by the block:
///
///   the MOTIVE, at index `num_params`, takes the indices and then the major,
///   so its own telescope is `num_indices + 1`
///   the MAJOR, the last binder, has a type headed by a block member
///
/// Both are what `reduce_recursor` relies on when it locates the major at
/// `nparams + nmotives + nminors + nindices` and matches its head against the
/// inductive. A decode that produced the right COUNTS over the wrong binders
/// passes the length check and breaks reduction.
///
/// Measured over `Init/Prelude` at private level: 129 recursors, every motive
/// telescope exactly `num_indices + 1`; 127 majors headed by a block member.
///
/// THE TWO THAT ARE NOT are the nested auxiliaries, and their majors are headed
/// by the NESTING CONTAINERS — `Array` for `rec_1`, `List` for `rec_2` — which
/// is what recursing over `Array Syntax` and `List Syntax` means. They are
/// pinned by container rather than skipped, so a nested recursor whose major
/// drifted to something else still fails.
#[test]
fn the_recursor_telescope_binds_a_motive_and_a_major_of_the_right_shape() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut checked = 0usize;
    let mut argument_counts: BTreeSet<usize> = BTreeSet::new();
    for info in &infos {
        let ConstantInfo::Rec(rec) = info else {
            continue;
        };
        let name = info.name().to_display_string();
        let domains = all_domains(&rec.base.type_);
        let block: BTreeSet<String> = rec.all.iter().map(Name::to_display_string).collect();

        // The motive sits immediately after the parameters.
        let motive = domains
            .get(rec.num_params as usize)
            .unwrap_or_else(|| panic!("{name}: telescope has no motive binder"));
        assert_eq!(
            telescope_length(motive),
            (rec.num_indices + 1) as usize,
            "{name}: the motive takes the indices and then the major"
        );

        // The major is the last binder.
        let major_index =
            (rec.num_params + rec.num_motives + rec.num_minors + rec.num_indices) as usize;
        let major = domains
            .get(major_index)
            .unwrap_or_else(|| panic!("{name}: telescope has no major premise"));
        let mut current = *major;
        let mut arguments = 0usize;
        while let ExprNode::App { f, .. } = current.node() {
            arguments += 1;
            current = f;
        }
        let ExprNode::Const { name: head, .. } = current.node() else {
            panic!("{name}: the major premise is not headed by a constant");
        };
        argument_counts.insert(arguments);

        let head = head.to_display_string();
        match NESTED_MAJOR_CONTAINERS
            .iter()
            .find(|(recursor, _)| *recursor == name)
        {
            Some((_, container)) => assert_eq!(
                head, *container,
                "{name} recurses over a nesting container, so its major is headed by that \
                 container and by nothing else"
            ),
            None => assert!(
                block.contains(&head),
                "{name}: the major premise must be headed by a member of its own block, which \
                 is what reduce_recursor matches against; got {head}"
            ),
        }
        checked += 1;
    }

    // Non-vacuity: the major's head is applied to a varying number of arguments,
    // so this is not one shape repeated.
    assert!(
        checked >= 120 && argument_counts.len() >= 4,
        "the recursor census must be reached with varied majors ({checked} recursors, {} \
         distinct argument counts)",
        argument_counts.len()
    );
}

/// Each quotient kind, and the type shape `quot_reduce_rec` assumes for it.
///
/// Columns are (kind, telescope length, index of the `Quot`-headed binder).
/// Those indices are not decoration — they are the literal constants the kernel
/// dispatches on: `quot_reduce_rec` reads the `Quot.mk` argument at position 5
/// for `Lift` and 4 for `Ind`, and applies the function or motive taken from
/// position 3 in both cases.
const QUOTIENT_SHAPES: &[(QuotKind, usize, Option<usize>)] = &[
    (QuotKind::Type, 2, None),
    (QuotKind::Ctor, 3, None),
    (QuotKind::Lift, 6, Some(5)),
    (QuotKind::Ind, 5, Some(4)),
];

/// The quotient constants' types agree with the positions the kernel reduces at.
///
/// `45202876` pinned each quotient constant's `kind`. Nothing checked what that
/// kind IMPLIES about its type — and the kernel's quotient reduction is written
/// against the implication rather than against the kind alone. `quot_reduce_rec`
/// locates the `Quot.mk` argument at a hardcoded index that depends only on the
/// kind, and takes the function or motive from index 3. If the pin's quotient
/// signatures ever moved, those constants would silently point at the wrong
/// arguments: the reduction would still fire, on the wrong terms.
///
/// So this is a relation between two things already read separately — the stored
/// `kind` and the decoded type — and it binds them at exactly the positions the
/// kernel hardcodes.
///
/// Measured over `Init/Prelude` at private level: `Quot` takes 2 binders and
/// `Quot.mk` 3, neither carrying a `Quot`-headed argument; `Quot.lift` takes 6
/// with its `Quot` argument at index 5; `Quot.ind` takes 5 with its `Quot`
/// argument at index 4. Both eliminators carry exactly one `Quot`-headed binder,
/// and in both the binder at index 3 is a function type — the thing the
/// reduction applies.
#[test]
fn quotient_types_place_their_arguments_where_the_kernel_reduces() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut seen = 0usize;
    for info in &infos {
        let ConstantInfo::Quot(quot) = info else {
            continue;
        };
        let name = info.name().to_display_string();
        let (_, expected_len, quot_index) = QUOTIENT_SHAPES
            .iter()
            .find(|(kind, _, _)| *kind == quot.kind)
            .unwrap_or_else(|| panic!("{name}: unexpected quotient kind {:?}", quot.kind));

        let domains = all_domains(&info.constant_val().type_);
        assert_eq!(
            domains.len(),
            *expected_len,
            "{name} ({:?}): telescope length is what the reduction's argument indices are \
             relative to",
            quot.kind
        );

        let quot_headed: Vec<usize> = domains
            .iter()
            .enumerate()
            .filter(|(_, domain)| {
                let mut current = **domain;
                while let ExprNode::App { f, .. } = current.node() {
                    current = f;
                }
                matches!(current.node(), ExprNode::Const { name, .. } if name.to_display_string() == "Quot")
            })
            .map(|(index, _)| index)
            .collect();

        match quot_index {
            Some(index) => {
                assert_eq!(
                    quot_headed,
                    vec![*index],
                    "{name} ({:?}): the kernel reads its Quot.mk argument at this index and \
                     nowhere else",
                    quot.kind
                );
                // Index 3 is the function (`Lift`) or motive proof (`Ind`) the
                // reduction applies; both are function types at the pin.
                assert!(
                    matches!(domains[3].node(), ExprNode::ForallE { .. }),
                    "{name} ({:?}): the argument the reduction applies must be a function type",
                    quot.kind
                );
            }
            None => assert!(
                quot_headed.is_empty(),
                "{name} ({:?}): carries no Quot-headed argument at the pin, got {quot_headed:?}",
                quot.kind
            ),
        }
        seen += 1;
    }
    assert_eq!(
        seen,
        QUOTIENT_SHAPES.len(),
        "every quotient kind must be present, or a shape above is never exercised"
    );
}

/// The mutual definition groups at the pin — and every one is this bead's
/// `.loop` family.
const MUTUAL_DEFINITION_GROUPS: &[[&str; 2]] = &[
    [
        "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop",
        "Lean.Syntax.getHeadInfo?",
    ],
    [
        "_private.Init.Prelude.0.Lean.Syntax.getHeadInfo?.loop._unsafe_rec",
        "Lean.Syntax.getHeadInfo?._unsafe_rec",
    ],
    [
        "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop",
        "Lean.Syntax.getTailPos?",
    ],
    [
        "_private.Init.Prelude.0.Lean.Syntax.getTailPos?.loop._unsafe_rec",
        "Lean.Syntax.getTailPos?._unsafe_rec",
    ],
];

/// `all` on the VALUE-carrying declarations — the surface the block-list cell
/// did not cover, and the one where mutual groups actually exist.
///
/// `15252a2f` checked `all` on inductives, recursors and constructors, and had
/// to disclose that every block in the corpus is a singleton, so its coherence
/// law was unexercised. Definitions, theorems and opaques carry an `all` too,
/// for mutual recursion, and nothing here read it.
///
/// That surface is NOT degenerate. `Init/Prelude` carries 1,887 value-carrying
/// declarations, 8 of them in 4 groups of two — so the same coherence law is
/// genuinely exercised on multi-member groups here, which is exactly what the
/// inductive side could not do.
///
/// AND ALL FOUR GROUPS ARE THIS BEAD'S OWN FAMILY. Every one pairs a `.loop`
/// auxiliary with the function it implements — the `.loop` family the filing
/// text named alongside `match_N` and `_proof_N`. Two of the four contain
/// `Lean.Syntax.getHeadInfo?._unsafe_rec` and `getTailPos?._unsafe_rec`, which
/// are two of the six `ArtifactIncomplete` rows pinned above; those rows report
/// a missing `.match_1`, and the declarations reporting them turn out to be
/// mutually recursive with the very `.loop` auxiliaries the private part
/// restores.
#[test]
fn value_carrying_declarations_agree_on_their_mutual_groups() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut groups: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for info in &infos {
        let all = match info {
            ConstantInfo::Defn(v) => &v.all,
            ConstantInfo::Thm(v) => &v.all,
            ConstantInfo::Opaque(v) => &v.all,
            _ => continue,
        };
        groups.insert(
            info.name().to_display_string(),
            all.iter().map(Name::to_display_string).collect(),
        );
    }
    assert!(
        groups.len() > 1_500,
        "the value-carrying census must be reached, got {}",
        groups.len()
    );

    for (name, all) in &groups {
        assert!(
            all.contains(name),
            "{name}: a declaration must be a member of its own mutual group"
        );
        for member in all {
            assert_eq!(
                groups.get(member),
                Some(all),
                "{name}: group member {member} declares a different group, so the kernel would \
                 admit the two under different blocks"
            );
        }
    }

    // The multi-member population, which is what makes the law above more than
    // a restatement of `all == [self]`. The inductive side of this check has no
    // such population anywhere in the corpus.
    let mut mutual: Vec<Vec<String>> = groups
        .values()
        .filter(|all| all.len() > 1)
        .cloned()
        .collect();
    mutual.sort();
    mutual.dedup();
    let expected: Vec<Vec<String>> = MUTUAL_DEFINITION_GROUPS
        .iter()
        .map(|group| group.iter().map(|n| (*n).to_string()).collect())
        .collect();
    assert_eq!(
        mutual, expected,
        "the mutual definition groups at the pin; every one pairs a `.loop` auxiliary with the \
         function it implements, and a new group is a new member of that family"
    );
}

/// Constructors whose name is NOT an extension of their inductive's, with the
/// inductive each belongs to.
///
/// Two distinct shapes, and neither is a defect:
///
///   three `_impl` compiler representations, where the `_impl` suffix is applied
///   to the BASE name rather than appended after the constructor — the inductive
///   is `Lean.Name._impl` while its constructors are `Lean.Name.str._impl` and
///   friends, so neither name is a prefix of the other
///
///   one genuinely PRIVATE constructor of a PUBLIC inductive:
///   `_private.Init.Prelude.0.Lean.Macro.State.mk` constructs `Lean.Macro.State`
const CONSTRUCTORS_NOT_UNDER_THEIR_INDUCTIVE: &[(&str, &str)] = &[
    ("Lean.Name.anonymous._impl", "Lean.Name._impl"),
    ("Lean.Name.num._impl", "Lean.Name._impl"),
    ("Lean.Name.str._impl", "Lean.Name._impl"),
    (
        "_private.Init.Prelude.0.Lean.Macro.State.mk",
        "Lean.Macro.State",
    ),
];

/// The name relation between a block's declarations — tested rather than
/// assumed, and false for constructors.
///
/// "A constructor is named under its inductive" is the kind of rule that reads
/// as obviously true and gets used as a lookup key. This file has been bitten
/// three times by keying on a name shape instead of a stored relation, so the
/// rule is worth checking rather than believing.
///
/// It holds for RECURSORS without exception: all 129 are their block head's name
/// extended by exactly `rec`, `rec_1` or `rec_2`, and no other suffix occurs.
///
/// It is FALSE for constructors — 4 of 157 are not under their inductive at all,
/// in the two shapes named above. The private one is the interesting member:
/// `_private.Init.Prelude.0.Lean.Macro.State.mk` constructs the PUBLIC
/// `Lean.Macro.State`, so the private-name machinery applies at CONSTRUCTOR
/// granularity, not only at declaration granularity. Anything resolving a
/// constructor by prefixing its inductive's name would miss it — and this bead's
/// whole subject is declarations that went missing because a lookup did not find
/// them.
///
/// The exceptions are pinned by name with their inductives, so a fifth is a
/// change in the artifact rather than more of the same.
#[test]
fn recursors_are_named_under_their_block_but_constructors_are_not_always() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut recursor_suffixes: BTreeSet<String> = BTreeSet::new();
    let mut recursors = 0usize;
    let mut constructors = 0usize;
    let mut outside: Vec<(String, String)> = Vec::new();
    for info in &infos {
        let name = info.name().to_display_string();
        match info {
            ConstantInfo::Rec(v) => {
                recursors += 1;
                let head = v.all[0].to_display_string();
                let prefix = format!("{head}.");
                assert!(
                    name.starts_with(&prefix),
                    "{name}: a recursor is named under its block head {head}"
                );
                recursor_suffixes.insert(name[prefix.len()..].to_string());
            }
            ConstantInfo::Ctor(v) => {
                constructors += 1;
                let induct = v.induct.to_display_string();
                if !name.starts_with(&format!("{induct}.")) {
                    outside.push((name, induct));
                }
            }
            _ => {}
        }
    }

    assert!(
        recursors >= 120 && constructors >= 150,
        "both censuses must be reached ({recursors} recursors, {constructors} constructors)"
    );
    assert_eq!(
        recursor_suffixes
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>(),
        vec!["rec", "rec_1", "rec_2"],
        "the only recursor suffixes at the pin; a new one is a new generation shape"
    );

    outside.sort();
    let expected: Vec<(String, String)> = CONSTRUCTORS_NOT_UNDER_THEIR_INDUCTIVE
        .iter()
        .map(|(ctor, induct)| ((*ctor).to_string(), (*induct).to_string()))
        .collect();
    assert_eq!(
        outside, expected,
        "the constructors not named under their inductive. This set being NON-EMPTY is the \
         point: a resolver that reached a constructor by prefixing its inductive's name would \
         miss every one of them, and one of them is private while its inductive is not."
    );
}

/// The generated binder names inside a recursor's type.
///
/// Binder names do not affect defeq, so it would be easy to treat them as
/// cosmetic. They are not cosmetic here: recursor comparison at admission is
/// BYTE-EXACT, so the names Lean generates are part of what a regeneration has
/// to reproduce — and a regeneration that differs from the decoded recursor is a
/// `BlockMismatch`, which is the family this bead's 228 rows came from.
///
/// Three generated names, measured over `Init/Prelude` at private level:
///
///   the MAJOR binder is `t`, in all 129 recursors without exception
///   the MOTIVE binder is `motive` when there is one, `motive_1` when there are
///     several — 129 of 129
///   each MINOR binder is its constructor's name with the inductive's prefix
///     STRIPPED
///
/// THE MINOR RULE IS THE INTERESTING ONE, because its fallback is exactly the
/// population the naming cell above refutes. When a constructor is not under its
/// inductive, there is no prefix to strip, and Lean names the binder with the
/// FULL constructor name instead: `Lean.Macro.State.rec` binds
/// `_private.Init.Prelude.0.Lean.Macro.State.mk`, and `Lean.Name._impl.rec`
/// binds `Lean.Name.anonymous._impl` and its siblings.
///
/// So the four constructors that broke the naming relation in the cell above
/// reappear here, in a different field, producing exactly the deviation that
/// relation predicts. Both facts are one phenomenon seen twice, and deriving the
/// expected binder name from the prefix rule — rather than from a leaf-name
/// shortcut — is what makes the two agree.
///
/// The three `Lean.Syntax` recursors are excluded from the minor comparison
/// alone: their minors cover the nested-expanded block, which `all` does not
/// name, so there is nothing here to compare against. Their major and motive
/// names are still checked.
#[test]
fn recursor_binder_names_follow_the_generated_shape() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut ctors_of: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for info in &infos {
        if let ConstantInfo::Induct(v) = info {
            ctors_of.insert(
                info.name().to_display_string(),
                v.ctors.iter().map(Name::to_display_string).collect(),
            );
        }
    }

    let mut checked = 0usize;
    let mut compared_minors = 0usize;
    let mut fallbacks = 0usize;
    for info in &infos {
        let ConstantInfo::Rec(rec) = info else {
            continue;
        };
        let name = info.name().to_display_string();
        let binders: Vec<String> = {
            let mut out = Vec::new();
            let mut current = &rec.base.type_;
            while let ExprNode::ForallE {
                binder_name, body, ..
            } = current.node()
            {
                out.push(binder_name.to_display_string());
                current = body;
            }
            out
        };
        let params = rec.num_params as usize;
        let motives = rec.num_motives as usize;
        let minors = rec.num_minors as usize;

        assert_eq!(
            binders[params],
            if motives == 1 { "motive" } else { "motive_1" },
            "{name}: the motive binder is generated with a fixed name"
        );
        let major = params + motives + minors + rec.num_indices as usize;
        assert_eq!(
            binders[major], "t",
            "{name}: the major premise binder is generated as `t`"
        );
        checked += 1;

        if NESTED_NUMERIC_EXCEPTIONS.contains(&name.as_str()) {
            continue;
        }
        let induct = rec.all[0].to_display_string();
        let prefix = format!("{induct}.");
        let expected: Vec<String> = ctors_of
            .get(&induct)
            .expect("block head decodes")
            .iter()
            .map(|ctor| match ctor.strip_prefix(&prefix) {
                Some(rest) => rest.to_string(),
                None => {
                    fallbacks += 1;
                    ctor.clone()
                }
            })
            .collect();
        assert_eq!(
            binders[params + motives..params + motives + minors],
            expected[..],
            "{name}: each minor premise binder is its constructor's name with the inductive's \
             prefix stripped, and the FULL name where there is no prefix to strip"
        );
        compared_minors += 1;
    }

    assert!(
        checked >= 120 && compared_minors >= 120,
        "the recursor census must be reached ({checked} checked, {compared_minors} minors \
         compared)"
    );
    // The fallback must actually occur, or the prefix rule is indistinguishable
    // from a leaf-name shortcut over this artifact — and the leaf shortcut is
    // what a first attempt would write.
    assert!(
        fallbacks >= 4,
        "the full-name fallback must be exercised by the constructors that are not under their \
         inductive, got {fallbacks}"
    );
}

/// Constructors whose parameter binder NAMES differ from their inductive's.
///
/// Both are the `refl` constructor of a K-carrying equality, and in both the
/// INDUCTIVE side carries a macro-hygienic binder name while the constructor
/// side carries the plain one.
const HYGIENIC_PARAMETER_MISMATCHES: &[(&str, &str)] = &[("Eq.refl", "Eq"), ("HEq.refl", "HEq")];

/// Parameter binder NAMES across a block, which is a different question from
/// parameter binder TYPES.
///
/// `d1e0a3c4` compared the leading parameter DOMAINS of a constructor against
/// its inductive's and found them identical. Domains are what admission needs to
/// agree on; names are what byte-exact recursor comparison needs, since a
/// regenerated recursor takes its parameter binders from the inductive. The two
/// questions have different answers here, which is the reason to ask the second
/// one separately.
///
/// Measured over `Init/Prelude` at private level: of the 107 constructors whose
/// inductive takes parameters, 105 share its binder names exactly. The two that
/// do not are `Eq.refl` and `HEq.refl`, where the inductive's second parameter
/// is `a._@._internal._hyg.0` — a MACRO-HYGIENIC name — while the constructor's
/// is plain `a`.
///
/// The exceptions are characterised rather than merely listed: each is required
/// to differ ONLY by the inductive side carrying a hygiene marker. A different
/// kind of disagreement in the same place would fail, which a bare name list
/// would not catch.
///
/// Worth noting where they land. `Eq` and `HEq` are two of the three types whose
/// recursors carry K, so hygiene in binder names shows up precisely on the types
/// this bead's elimination work keeps returning to — and a regeneration that
/// normalised those names away would differ from the artifact byte-for-byte
/// while being semantically identical.
#[test]
fn constructors_share_their_inductives_parameter_binder_names_except_under_hygiene() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut inductives: BTreeMap<String, &InductiveVal> = BTreeMap::new();
    for info in &infos {
        if let ConstantInfo::Induct(v) = info {
            inductives.insert(info.name().to_display_string(), v);
        }
    }
    let binder_names = |type_: &Expr, count: usize| -> Vec<String> {
        let mut out = Vec::new();
        let mut current = type_;
        while out.len() < count {
            let ExprNode::ForallE {
                binder_name, body, ..
            } = current.node()
            else {
                break;
            };
            out.push(binder_name.to_display_string());
            current = body;
        }
        out
    };

    let mut agreeing = 0usize;
    let mut differing: Vec<(String, String)> = Vec::new();
    for info in &infos {
        let ConstantInfo::Ctor(ctor) = info else {
            continue;
        };
        let name = info.name().to_display_string();
        let induct_name = ctor.induct.to_display_string();
        let induct = inductives
            .get(&induct_name)
            .expect("constructor's inductive decodes");
        if induct.num_params == 0 {
            continue;
        }
        let count = induct.num_params as usize;
        let theirs = binder_names(&induct.base.type_, count);
        let mine = binder_names(&ctor.base.type_, count);
        if mine == theirs {
            agreeing += 1;
            continue;
        }
        // Characterise the disagreement: the inductive side must be the plain
        // name carrying a hygiene marker, and nothing else may differ.
        for (theirs, mine) in theirs.iter().zip(&mine) {
            if theirs == mine {
                continue;
            }
            assert!(
                theirs.starts_with(&format!("{mine}._@.")) && theirs.contains("_hyg"),
                "{name}: parameter binder `{mine}` differs from its inductive's `{theirs}` by \
                 something other than macro hygiene"
            );
        }
        differing.push((name, induct_name));
    }

    assert!(
        agreeing >= 100,
        "the parameter-name comparison must be exercised, got {agreeing} agreements"
    );
    differing.sort();
    let expected: Vec<(String, String)> = HYGIENIC_PARAMETER_MISMATCHES
        .iter()
        .map(|(ctor, induct)| ((*ctor).to_string(), (*induct).to_string()))
        .collect();
    assert_eq!(
        differing, expected,
        "the constructors whose parameter binder names differ from their inductive's; a new one \
         needs looking at rather than absorbing, since byte-exact recursor comparison reads \
         these names"
    );
}
