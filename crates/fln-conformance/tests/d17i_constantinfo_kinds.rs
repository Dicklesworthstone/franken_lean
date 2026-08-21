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

/// One-name-one-constant, and the `_impl` representation correspondence.
///
/// THE FIRST is the law KR-970 enforces at admission — `AlreadyDeclared` — and
/// nothing on the decode side had checked it. A module storing the same name
/// twice would give `add_decl` two constants for one name, and whichever
/// admission order the replay happened to use would decide which one the kernel
/// saw. Every reference and closure cell in this file would stay green through
/// that, because they all resolve names against a MAP built from these arrays,
/// and a map silently keeps the last writer.
///
/// Measured: 2,204 exported and 2,314 private names in `Init/Prelude`, 379 and
/// 530 in `Init/Meta/Defs`, all pairwise distinct at both levels.
///
/// THE SECOND explains an exception this file already records. `76c9b8dd` lists
/// three constructors that are not named under their inductive, all of the form
/// `Lean.Name.str._impl` under `Lean.Name._impl`. The reason is a systematic
/// correspondence rather than three oddities: `Lean.Name._impl` is the compiler
/// REPRESENTATION of `Lean.Name`, it carries the same number of constructors in
/// the same order, and each is the base constructor's name with `._impl`
/// appended. So the suffix lands after the CONSTRUCTOR, while the inductive got
/// it after its own base name — and neither name is a prefix of the other.
///
/// Stating it as a correspondence rather than a list means a second
/// representation pair is checked on arrival rather than being three more
/// unexplained names.
#[test]
fn names_are_unique_and_impl_representations_mirror_their_base() {
    let lib = lib_or_skip!();

    for module in ["Init.Prelude", "Init.Meta.Defs"] {
        for level in [Level::Exported, Level::Private] {
            let (infos, _) = decode_at(&lib, module, level);
            let names: Vec<String> = infos
                .iter()
                .map(|info| info.name().to_display_string())
                .collect();
            let distinct: BTreeSet<&String> = names.iter().collect();
            assert!(
                names.len() > 300,
                "{module}: the census must be reached, got {}",
                names.len()
            );
            assert_eq!(
                names.len(),
                distinct.len(),
                "{module}: a repeated constant name gives the kernel two constants for one \
                 name, and every name-keyed cell in this file would resolve to whichever was \
                 admitted last"
            );
        }
    }

    // The representation correspondence, stated for any `X._impl` whose base is
    // also a decoded inductive.
    let infos = decode_prelude_private(&lib);
    let mut inductives: BTreeMap<String, &InductiveVal> = BTreeMap::new();
    for info in &infos {
        if let ConstantInfo::Induct(v) = info {
            inductives.insert(info.name().to_display_string(), v);
        }
    }
    let mut pairs = 0usize;
    for (name, representation) in &inductives {
        let Some(base_name) = name.strip_suffix("._impl") else {
            continue;
        };
        let Some(base) = inductives.get(base_name) else {
            continue;
        };
        assert_eq!(
            representation.ctors.len(),
            base.ctors.len(),
            "{name}: a representation carries one constructor per base constructor"
        );
        for (mine, theirs) in representation.ctors.iter().zip(&base.ctors) {
            assert_eq!(
                mine.to_display_string(),
                format!("{}._impl", theirs.to_display_string()),
                "{name}: each representation constructor is its base constructor with `._impl` \
                 appended, which is why neither name is a prefix of the other"
            );
        }
        pairs += 1;
    }
    assert!(
        pairs >= 1,
        "the pin carries a representation pair; without one this correspondence is unexercised"
    );
}

/// The constant array is NOT in dependency order, and something has to know it.
///
/// Every other cell in this file treats the module's declarations as a set. They
/// are stored as an ARRAY, and `decode_module_constants` returns them in that
/// order — so the tempting simplification, for any consumer, is to admit them in
/// the order they arrive.
///
/// That would fail immediately. Measured over `Init/Prelude` at private level:
/// 6,680 references point FORWARD, to a declaration stored later in the same
/// array. The very first declaration is one of them — `HXor.recOn` sits at index
/// 0 and references `HXor` at index 2048 — so sequential admission does not
/// survive its own first step, and it fails as `UnknownConstant`, which is this
/// bead's own reject class.
///
/// This is why `OleanCheckLimits` carries `max_dependency_presentations` to
/// bound "the iterative walk used to recover a deterministic declaration order":
/// the artifact does not supply an admission order, and the pipeline recovers
/// one. Nothing recorded that the recovery is load-bearing rather than a
/// convenience.
///
/// So this cell asserts a NEGATIVE, which is unusual here and deliberate. The
/// floor is on forward references EXISTING in bulk: if a future change made the
/// array dependency-ordered, this fails and someone re-reads the ordering
/// machinery on purpose rather than discovering by accident that it had become
/// dead code. And if the array is ever consumed in order, the failure is not
/// subtle — it is 6,680 unknown constants.
#[test]
fn the_constant_array_is_not_in_dependency_order() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let position: BTreeMap<String, usize> = infos
        .iter()
        .enumerate()
        .map(|(index, info)| (info.name().to_display_string(), index))
        .collect();

    let mut forward = 0usize;
    let mut intra_module = 0usize;
    let mut first_forward: Option<(String, String, usize)> = None;
    for (index, info) in infos.iter().enumerate() {
        let mut referenced = BTreeSet::new();
        for expr in declaration_expressions(info) {
            referenced.append(&mut referenced_constants(expr));
        }
        for name in &referenced {
            let Some(target) = position.get(name) else {
                continue;
            };
            intra_module += 1;
            if *target > index {
                forward += 1;
                if first_forward.is_none() {
                    first_forward = Some((info.name().to_display_string(), name.clone(), *target));
                }
            }
        }
    }

    // Anti-vacuity: a reference scan that found nothing would report zero
    // forward references and satisfy a naive "is it ordered" check instead.
    assert!(
        intra_module > 10_000,
        "the scan must reach the module's intra-module references, got {intra_module}"
    );
    assert!(
        forward > 1_000,
        "the stored order is not a dependency order and consumers must not assume it is; \
         {forward} forward references"
    );
    let (referrer, target, target_index) =
        first_forward.expect("a forward reference must exist to name");
    assert!(
        target_index > 1_000,
        "the first forward reference reaches far down the array — {referrer} to {target} at \
         index {target_index} — so admitting in array order fails at the first declaration, \
         with UnknownConstant"
    );
}

/// The private part re-serialises the module; it is not the exported array with
/// additions.
///
/// The containment cell established that no name is lost between the levels, and
/// several cells compare the two parts. All of them compare by NAME. Nothing
/// said why that is the only option — and "the private part is the exported one
/// plus the private extras" is the natural mental model, under which a positional
/// shortcut would work: take the tail, or diff by index.
///
/// It is wrong. Measured over `Init/Prelude` and `Init/Meta/Defs` at both
/// levels:
///
///   the exported array is NOT a prefix of the private array
///   the exported names do NOT appear in the private array in their exported
///     order — the positions are not even monotonically increasing
///   the private-only declarations are INTERLEAVED throughout, starting near the
///     top: Prelude's first extra sits at private index 13, Meta.Defs' at index 1
///
/// In `Init/Prelude` the 2,204 exported names land across private indices 1157
/// to 2312, so the two arrays share no positional structure at all. The private
/// part is a fresh serialisation of the whole module.
///
/// Like the dependency-order cell, this asserts a NEGATIVE on purpose. Every
/// exported/private comparison in this file is name-keyed; if the arrays ever
/// did line up positionally, someone could reasonably simplify those comparisons
/// to index arithmetic, and this fails first so that change is made knowingly
/// rather than because it happened to work on one module.
#[test]
fn the_private_part_reserialises_rather_than_extends_the_exported_array() {
    let lib = lib_or_skip!();

    for module in ["Init.Prelude", "Init.Meta.Defs"] {
        let (exported_infos, _) = decode_at(&lib, module, Level::Exported);
        let (private_infos, _) = decode_at(&lib, module, Level::Private);
        let exported: Vec<String> = exported_infos
            .iter()
            .map(|info| info.name().to_display_string())
            .collect();
        let private: Vec<String> = private_infos
            .iter()
            .map(|info| info.name().to_display_string())
            .collect();
        assert!(
            exported.len() > 100 && private.len() > exported.len(),
            "{module}: both arrays must be substantial ({} exported, {} private)",
            exported.len(),
            private.len()
        );

        assert_ne!(
            private[..exported.len()],
            exported[..],
            "{module}: the private array is not the exported one with extras appended"
        );

        let position: BTreeMap<&String, usize> = private
            .iter()
            .enumerate()
            .map(|(index, name)| (name, index))
            .collect();
        let positions: Vec<usize> = exported
            .iter()
            .map(|name| {
                *position
                    .get(name)
                    .unwrap_or_else(|| panic!("{module}: {name} is absent from the private array"))
            })
            .collect();
        assert!(
            positions.windows(2).any(|pair| pair[0] > pair[1]),
            "{module}: the exported order is not preserved in the private array, so no \
             positional comparison between the two levels is valid"
        );

        // The extras are interleaved, not tacked on: at least one private-only
        // declaration precedes at least one exported one.
        let exported_set: BTreeSet<&String> = exported.iter().collect();
        let first_extra = private
            .iter()
            .position(|name| !exported_set.contains(name))
            .expect("the private part adds declarations");
        assert!(
            positions.iter().any(|index| *index > first_extra),
            "{module}: private-only declarations are interleaved with exported ones, so the \
             private set cannot be recovered as a suffix"
        );
    }
}

/// Inductives with no generated `recOn`.
const WITHOUT_REC_ON: &[&str] = &["Lean.Name._impl", "Nat.le.below"];
/// Non-Prop inductives with no generated `noConfusion`.
const NON_PROP_WITHOUT_NO_CONFUSION: &[&str] = &["Lean.Name._impl", "PUnit"];

/// The generated ELIMINATOR family, which is auxiliary declarations of exactly
/// the kind this bead is about — and no cell had looked at it.
///
/// Every cell so far reads declarations Lean stores for an inductive block:
/// the type, its constructors, its recursor. Lean also GENERATES a family of
/// ordinary definitions around each inductive — `casesOn`, `recOn`,
/// `noConfusion`, `below`, `brecOn` — and whether they are present is a function
/// of fields this file already reads. Four relations, all exact over
/// `Init/Prelude` at private level:
///
///   `casesOn` exists for ALL 127 inductives, without exception
///   `recOn` exists for all but two, named above
///   `noConfusion` exists for 115, and NONE of those 115 is a Prop — so being a
///     Prop implies having no `noConfusion`. The converse fails: two non-Props
///     lack it too, and they are named
///   `below` and `brecOn` exist for exactly the RECURSIVE inductives that are
///     not themselves a generated `.below` type — 6 of the 7, the exception
///     being `Nat.le.below`
///
/// The `noConfusion` rule is stated as a ONE-WAY implication because that is
/// what the artifact supports. An `iff` would be false, and writing one would
/// have been the easy mistake: 10 of the 12 absences are Props, which reads as a
/// clean biconditional until the other two are looked at.
///
/// The `below` rule IS an iff, and it is worth having as one: it ties a
/// generated declaration's existence to `is_rec`, a stored flag, so a decode
/// that lost `is_rec` would be caught by the presence of declarations it no
/// longer predicts.
#[test]
fn the_generated_eliminator_family_follows_from_fields_already_read() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let names: BTreeSet<String> = infos
        .iter()
        .map(|info| info.name().to_display_string())
        .collect();
    let mut inductives: BTreeMap<String, &InductiveVal> = BTreeMap::new();
    for info in &infos {
        if let ConstantInfo::Induct(v) = info {
            inductives.insert(info.name().to_display_string(), v);
        }
    }
    assert!(
        inductives.len() > 100,
        "the inductive census must be reached, got {}",
        inductives.len()
    );

    let mut missing_rec_on: Vec<&String> = Vec::new();
    let mut no_confusion_props = 0usize;
    let mut non_prop_without: Vec<&String> = Vec::new();
    let mut with_below: Vec<&String> = Vec::new();
    let mut recursive = 0usize;
    for (name, induct) in &inductives {
        let has = |suffix: &str| names.contains(&format!("{name}.{suffix}"));

        assert!(
            has("casesOn"),
            "{name}: every inductive gets a generated casesOn"
        );
        if !has("recOn") {
            missing_rec_on.push(name);
        }

        let prop = inductive_result_is_prop(induct);
        if has("noConfusion") {
            assert!(
                has("noConfusionType"),
                "{name}: noConfusion and noConfusionType are generated together"
            );
            if prop {
                no_confusion_props += 1;
            }
        } else if !prop {
            non_prop_without.push(name);
        }

        if induct.is_rec {
            recursive += 1;
        }
        // `below` exists exactly for recursive inductives that are not
        // themselves a generated `.below` type.
        let expected_below = induct.is_rec && !name.ends_with(".below");
        assert_eq!(
            has("below"),
            expected_below,
            "{name}: `below` is generated for recursive inductives and not for the `.below` \
             types that generation itself produces"
        );
        assert_eq!(
            has("brecOn"),
            expected_below,
            "{name}: `brecOn` accompanies `below`"
        );
        if has("below") {
            with_below.push(name);
        }
    }

    assert_eq!(
        no_confusion_props, 0,
        "a Prop inductive must not carry a generated noConfusion"
    );
    assert_eq!(missing_rec_on, WITHOUT_REC_ON);
    assert_eq!(non_prop_without, NON_PROP_WITHOUT_NO_CONFUSION);
    // Non-vacuity for the `below` iff: both sides of it must be populated.
    assert!(
        recursive >= 5 && with_below.len() >= 5 && with_below.len() < inductives.len(),
        "the recursive population must be real ({recursive} recursive, {} with below of {})",
        with_below.len(),
        inductives.len()
    );
}

/// Members of the generated eliminator family that are not stored as
/// definitions, with the kind each is stored as instead.
const NON_DEFINITION_ELIMINATORS: &[(&str, &str)] =
    &[("Nat.le.below", "Induct"), ("Nat.le.brecOn", "Thm")];

/// What a generated eliminator's VALUE contains and how it unfolds — two stored
/// fields nothing had read for this family.
///
/// The cell above asserts only that these declarations EXIST. A `casesOn` whose
/// body had been replaced by an unrelated constant satisfies it, and satisfies
/// the reference-closure cells too: those require every referenced name to
/// resolve and say nothing about WHICH names appear. Three exact relations over
/// `Init/Prelude` at private level:
///
///   Every member stored as a definition carries `ReducibilityHints::Abbrev` —
///     127 `casesOn`, 125 `recOn`, 115 `noConfusion`, 115 `noConfusionType`, 5
///     `below`, 5 `brecOn`; 492 declarations, no exception. Not vacuous: of the
///     module's 1,720 definitions 549 are `Regular` or `Opaque`.
///
///   Every `casesOn` and `recOn` value references EXACTLY ONE recursor, and it
///     is its own inductive's. The claim is deliberately not "the set contains
///     `X.rec`", which a walk returning too much would also satisfy; pinning the
///     count to one makes the walk's precision part of what is asserted.
///
///   `noConfusion` delegates to `noConfusionType`, and `brecOn` to `below` —
///     0 missing of 115 and of 6.
///
/// The family is also NOT kind-uniform, and that is the fact underneath the
/// exception in the cell above: `Nat.le.below` is an INDUCTIVE and
/// `Nat.le.brecOn` a THEOREM. `Nat.le` is a Prop, so its `below` is generated as
/// an inductive family rather than a definition and its `brecOn` proves a
/// proposition rather than computing one. `Nat.le.below` being an inductive is
/// exactly why it is itself an inductive needing no `below`, which is the shape
/// the `below` iff carves out by name.
#[test]
fn generated_eliminators_are_abbreviations_that_delegate_to_their_recursor() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);
    let all_kinds = kinds(&infos);

    let mut inductives: BTreeSet<String> = BTreeSet::new();
    let mut recursors: BTreeSet<String> = BTreeSet::new();
    let mut definitions: BTreeMap<String, (&ReducibilityHints, &Expr)> = BTreeMap::new();
    let mut values: BTreeMap<String, &Expr> = BTreeMap::new();
    let mut not_abbrev_elsewhere = 0usize;
    for info in &infos {
        let name = info.name().to_display_string();
        match info {
            ConstantInfo::Induct(_) => drop(inductives.insert(name)),
            ConstantInfo::Rec(_) => drop(recursors.insert(name)),
            ConstantInfo::Thm(v) => drop(values.insert(name, &v.value)),
            ConstantInfo::Defn(v) => {
                if !matches!(v.hints, ReducibilityHints::Abbrev) {
                    not_abbrev_elsewhere += 1;
                }
                values.insert(name.clone(), &v.value);
                definitions.insert(name, (&v.hints, &v.value));
            }
            _ => {}
        }
    }
    assert!(
        inductives.len() > 100 && recursors.len() > 100,
        "the inductive and recursor censuses must be reached, got {} and {}",
        inductives.len(),
        recursors.len()
    );

    const SUFFIXES: [&str; 6] = [
        "casesOn",
        "recOn",
        "noConfusion",
        "noConfusionType",
        "below",
        "brecOn",
    ];
    let mut abbrev: BTreeMap<&str, usize> = BTreeMap::new();
    let mut not_abbrev: Vec<String> = Vec::new();
    let mut non_definition: Vec<(String, &'static str)> = Vec::new();
    let mut wrong_recursor_count: Vec<(String, usize)> = Vec::new();
    let mut foreign_recursor: Vec<String> = Vec::new();
    let mut missing_delegate: Vec<String> = Vec::new();
    let mut delegated = 0usize;

    for inductive in &inductives {
        for suffix in SUFFIXES {
            let member = format!("{inductive}.{suffix}");
            let Some(kind) = all_kinds.get(&member) else {
                continue;
            };
            match definitions.get(&member) {
                Some((hints, _)) => {
                    if matches!(hints, ReducibilityHints::Abbrev) {
                        *abbrev.entry(suffix).or_default() += 1;
                    } else {
                        not_abbrev.push(member.clone());
                    }
                }
                None => non_definition.push((member.clone(), kind)),
            }

            // The delegation each generated member owes to the declaration it
            // is built from. `below` is generated from the inductive's own
            // constructors and owes nothing, so it is not listed here.
            let delegate = match suffix {
                "casesOn" | "recOn" => format!("{inductive}.rec"),
                "noConfusion" => format!("{inductive}.noConfusionType"),
                "brecOn" => format!("{inductive}.below"),
                _ => continue,
            };
            let Some(value) = values.get(&member) else {
                continue;
            };
            let referenced = referenced_constants(value);
            if !referenced.contains(&delegate) {
                missing_delegate.push(member.clone());
            } else {
                delegated += 1;
            }
            if matches!(suffix, "casesOn" | "recOn") {
                let seen: Vec<&String> = referenced.intersection(&recursors).collect();
                if seen.len() != 1 {
                    wrong_recursor_count.push((member.clone(), seen.len()));
                } else if *seen[0] != delegate {
                    foreign_recursor.push(member);
                }
            }
        }
    }

    assert!(
        not_abbrev.is_empty(),
        "every generated eliminator stored as a definition is an abbreviation; these are not: {not_abbrev:?}"
    );
    let counted: usize = abbrev.values().sum();
    assert_eq!(
        counted, 492,
        "the abbreviation census must be complete, got {abbrev:?}"
    );
    // Non-vacuity: `Abbrev` is a minority verdict over the module, so a decoder
    // answering `Abbrev` for everything would be caught here rather than
    // silently satisfying the assertion above.
    assert!(
        not_abbrev_elsewhere > 400,
        "abbreviation must not be the universal hint, got {not_abbrev_elsewhere} others"
    );

    assert!(
        wrong_recursor_count.is_empty() && foreign_recursor.is_empty(),
        "a casesOn/recOn value names exactly one recursor, its own: {wrong_recursor_count:?} \
         {foreign_recursor:?}"
    );
    assert!(
        missing_delegate.is_empty(),
        "these generated eliminators do not reference the declaration they are built from: \
         {missing_delegate:?}"
    );
    assert_eq!(
        delegated, 373,
        "the delegation census must be complete (127 casesOn, 125 recOn, 115 noConfusion, \
         6 brecOn)"
    );

    let observed: Vec<(&str, &str)> = non_definition
        .iter()
        .map(|(name, kind)| (name.as_str(), *kind))
        .collect();
    assert_eq!(
        observed, NON_DEFINITION_ELIMINATORS,
        "the generated family is not kind-uniform, and these are the members that depart"
    );
}

/// Every stored expression is a CLOSED term, and no elaboration-time node
/// survives into the artifact.
///
/// Three `ExprNode` variants are walked past with `{ .. }` at every one of this
/// file's four walkers and asserted nowhere: `BVar`'s index, `FVar`, `MVar`.
/// That is the gap the comment above the projection cell already disclosed. It
/// matters because a de Bruijn index is the one part of a decoded expression
/// whose corruption is invisible to every other cell here: an off-by-one in
/// binder nesting still yields a well-typed `Expr`, still resolves every
/// constant reference, still matches every stored arity, and still round-trips
/// through the census. It shows up only as an index that escapes its binders.
///
/// Measured over `Init/Prelude` at private level, walking every stored
/// expression — 2,314 types, 1,887 values, 160 recursor rule right-hand sides,
/// 4,361 roots:
///
///   zero loose indices: every `BVar i` sits under at least `i + 1` binders
///   zero `FVar` and zero `MVar` — free variables and metavariables are
///     elaboration-time nodes and no stored declaration may contain one
///   deepest binder nesting 53, largest index 47
///
/// The bound is TIGHT, which is what keeps `idx < depth` from being a weak
/// claim: occurrences sit exactly at `idx == depth - 1`, so it cannot be
/// narrowed to `idx < depth - 1` without failing.
///
/// THE DEDUP IS THE SUBTLE PART. The other walkers key `seen` on
/// `allocation_identity()` alone, which is right for them — a reference set does
/// not depend on where a subterm sits. It is WRONG here. A shared subterm is
/// reachable at more than one depth, and skipping its shallower occurrence
/// discards exactly the visit where an index would be loose; the walk would run
/// clean over a corrupted artifact. `seen` is keyed on `(identity, depth)`.
#[test]
fn every_stored_expression_is_closed_and_carries_no_elaboration_nodes() {
    const CAP: usize = 2_000_000;
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut loose: Vec<(String, u32, u32)> = Vec::new();
    let mut elaboration_nodes: Vec<String> = Vec::new();
    let mut roots = 0usize;
    let mut visited = 0usize;
    let mut max_depth = 0u32;
    let mut max_index = 0u32;
    let mut tight = 0usize;

    for info in &infos {
        let name = info.name().to_display_string();
        for root in declaration_expressions(info) {
            roots += 1;
            let mut seen: BTreeSet<(usize, u32)> = BTreeSet::new();
            let mut stack: Vec<(&Expr, u32)> = vec![(root, 0)];
            while let Some((current, depth)) = stack.pop() {
                if !seen.insert((current.allocation_identity(), depth)) {
                    continue;
                }
                assert!(
                    seen.len() < CAP,
                    "{name}: scoped walk exceeded {CAP} node/depth pairs; raise the cap rather \
                     than trusting a truncated answer"
                );
                max_depth = max_depth.max(depth);
                match current.node() {
                    ExprNode::BVar { idx } => {
                        max_index = max_index.max(*idx);
                        if *idx >= depth {
                            loose.push((name.clone(), *idx, depth));
                        } else if *idx + 1 == depth {
                            tight += 1;
                        }
                    }
                    ExprNode::FVar { .. } | ExprNode::MVar { .. } => {
                        elaboration_nodes.push(name.clone());
                    }
                    ExprNode::App { f, a } => {
                        stack.push((f, depth));
                        stack.push((a, depth));
                    }
                    ExprNode::Lam {
                        binder_type, body, ..
                    }
                    | ExprNode::ForallE {
                        binder_type, body, ..
                    } => {
                        stack.push((binder_type, depth));
                        stack.push((body, depth + 1));
                    }
                    ExprNode::LetE {
                        type_, value, body, ..
                    } => {
                        stack.push((type_, depth));
                        stack.push((value, depth));
                        stack.push((body, depth + 1));
                    }
                    ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                        stack.push((expr, depth));
                    }
                    ExprNode::Sort { .. } | ExprNode::Const { .. } | ExprNode::Lit { .. } => {}
                }
            }
            visited += seen.len();
        }
    }

    assert!(
        loose.is_empty(),
        "these indices escape their binders (name, index, binders in scope): {:?}",
        &loose[..loose.len().min(8)]
    );
    assert!(
        elaboration_nodes.is_empty(),
        "no stored declaration may contain a free variable or metavariable; these do: {:?}",
        &elaboration_nodes[..elaboration_nodes.len().min(8)]
    );
    assert_eq!(
        roots, 4361,
        "every stored expression must be reached (2,314 types, 1,887 values, 160 rule right-hand \
         sides)"
    );
    // The walk must be real, and the bound it checks must be tight. Both of
    // these are what stop `idx < depth` from passing over an empty or shallow
    // traversal.
    assert!(
        visited > 100_000,
        "the scoped walk must cover the module, got {visited} node/depth pairs"
    );
    assert_eq!(
        (max_depth, max_index),
        (53, 47),
        "the binder nesting and index range are exact, and independent of how the decoder shares \
         subterms"
    );
    assert!(
        tight > 1_000,
        "the bound must be tight — indices sitting exactly at depth - 1 are what forbid \
         narrowing it, got {tight}"
    );
}

/// Every level a stored expression carries, through both carriers: a `Sort`'s
/// level and a `Const`'s level arguments.
fn stored_levels(root: &Expr) -> Vec<&fln_core::level::Level> {
    let mut out = Vec::new();
    let mut seen: BTreeSet<usize> = BTreeSet::new();
    let mut stack: Vec<&Expr> = vec![root];
    while let Some(current) = stack.pop() {
        if !seen.insert(current.allocation_identity()) {
            continue;
        }
        match current.node() {
            ExprNode::Sort { level } => out.push(level),
            ExprNode::Const { levels, .. } => out.extend(levels.iter()),
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
            | ExprNode::Lit { .. } => {}
        }
    }
    out
}

/// The form a normalizing level constructor would have collapsed, or `None`.
fn collapsible_form(level: &fln_core::level::Level) -> Option<&'static str> {
    match level.view() {
        LevelView::IMax(u, v) => match v.view() {
            LevelView::Zero => Some("imax _ 0 collapses to 0"),
            LevelView::Succ(_) => Some("imax u (succ v) collapses to max u (succ v)"),
            _ => (u == v).then_some("imax u u collapses to u"),
        },
        LevelView::Max(a, b) => {
            if matches!(a.view(), LevelView::Zero) || matches!(b.view(), LevelView::Zero) {
                Some("max with 0 collapses to the other side")
            } else {
                (a == b).then_some("max u u collapses to u")
            }
        }
        _ => None,
    }
}

/// No stored level is in a form a normalizing constructor would have collapsed
/// — the artifact-side half of this bead's own root cause.
///
/// The level cell above reads level parameters as NAMES and settles KR-140 and
/// KR-971. It says nothing about level STRUCTURE, and structure is where d17i
/// actually lives: the 228 rows were traced to `infer` minting a `Pi` sort with
/// a dumb `imax` where the pin uses a normalizing constructor, so `imax _ 0`
/// survived instead of collapsing to `0` and large elimination was refused.
/// That was settled in the kernel. What was never asserted is the artifact fact
/// that makes it a divergence at all: the pin does not STORE levels in those
/// forms, so a path that produces one is producing something no `.olean` at the
/// pin contains.
///
/// Measured over `Init/Prelude` at private level, every level reachable from
/// every stored expression through both carriers — 35,225 level nodes: 19,096
/// `Param`, 9,878 `Succ`, 4,323 `Zero`, 1,542 `Max`, 282 `IMax`, and ZERO
/// `MVar`. Five collapsible forms, all absent:
///
///   `imax _ 0`, `imax u (succ v)`, `imax u u`
///   `max` with a `0` on either side, `max u u`
///
/// What is asserted is the artifact fact, not a claim about upstream source:
/// these forms do not occur. The normalizing constructor is the explanation for
/// why, and the explanation is not what the cell checks.
///
/// The `MVar` count is the universe-level counterpart of the expression-level
/// law in the cell above, and it is a separate carrier: an expression free of
/// `FVar` and `MVar` can still carry a level metavariable inside a `Sort`,
/// because levels are not `ExprNode`s.
///
/// Counts are floors rather than equalities. A level is reached once per
/// distinct expression node carrying it, so the totals move with how the
/// decoder shares subterms; the absence of a form does not.
#[test]
fn no_stored_level_is_in_a_form_its_smart_constructor_would_have_collapsed() {
    const CAP: usize = 1_000_000;
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut shapes: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut collapsible: Vec<(String, &'static str)> = Vec::new();
    let mut metavariables: Vec<String> = Vec::new();
    let mut nodes = 0usize;

    for info in &infos {
        let name = info.name().to_display_string();
        for expr in declaration_expressions(info) {
            let mut stack: Vec<&fln_core::level::Level> = stored_levels(expr);
            while let Some(level) = stack.pop() {
                nodes += 1;
                assert!(
                    nodes < CAP,
                    "{name}: level walk exceeded {CAP} nodes; raise the cap rather than trusting \
                     a truncated answer"
                );
                if let Some(form) = collapsible_form(level) {
                    collapsible.push((name.clone(), form));
                }
                let shape = match level.view() {
                    LevelView::Zero => "Zero",
                    LevelView::Succ(inner) => {
                        stack.push(inner);
                        "Succ"
                    }
                    LevelView::Max(a, b) => {
                        stack.push(a);
                        stack.push(b);
                        "Max"
                    }
                    LevelView::IMax(a, b) => {
                        stack.push(a);
                        stack.push(b);
                        "IMax"
                    }
                    LevelView::Param(_) => "Param",
                    LevelView::MVar(_) => {
                        metavariables.push(name.clone());
                        "MVar"
                    }
                };
                *shapes.entry(shape).or_default() += 1;
            }
        }
    }

    assert!(
        collapsible.is_empty(),
        "these stored levels are in a form a normalizing constructor collapses: {:?}",
        &collapsible[..collapsible.len().min(8)]
    );
    assert!(
        metavariables.is_empty(),
        "a level metavariable is an elaboration-time node and no stored declaration may carry \
         one; these do: {:?}",
        &metavariables[..metavariables.len().min(8)]
    );

    // Anti-vacuity. Absence is only worth asserting over a population where the
    // constructors that could produce these forms are heavily used: a walk
    // finding no `IMax` at all would report the same empty violation list.
    let count = |shape: &str| shapes.get(shape).copied().unwrap_or_default();
    assert!(
        count("IMax") > 250 && count("Max") > 1_500,
        "both collapsible constructors must be well populated, got {shapes:?}"
    );
    assert!(
        count("Param") > 19_000 && count("Succ") > 9_000 && count("Zero") > 4_000,
        "the level population must be reached, got {shapes:?}"
    );
    assert_eq!(
        shapes.keys().copied().collect::<Vec<&str>>(),
        vec!["IMax", "Max", "Param", "Succ", "Zero"],
        "exactly five level shapes occur at the pin, and `MVar` is not one of them"
    );
}

/// `constNames` and `extraConstNames` read as NAMES, per module and level:
/// `(module, extra exported, extra private, overlap private)`.
const EXTRA_CONST_NAME_ROWS: &[(&str, usize, usize, usize)] = &[
    ("Init.Prelude", 424, 713, 0),
    ("Init.Meta.Defs", 192, 697, 1),
    ("Init.Data.List.Basic", 337, 443, 17),
    ("Init.Data.Array.Lemmas", 41, 106, 17),
];

/// Both header name arrays, at one level.
fn header_name_arrays(view: &OleanView<'_>) -> (Vec<String>, Vec<String>) {
    let declared = view
        .module_data(WalkBudget::default())
        .expect("module data")
        .const_names;
    let extra = view
        .extra_const_names(WalkBudget::default())
        .expect("extra const names")
        .iter()
        .map(Name::to_display_string)
        .collect();
    (declared, extra)
}

/// Read `constNames` and `extraConstNames` as name arrays rather than counts.
fn header_names(lib: &Path, module: &str, level: Level) -> (Vec<String>, Vec<String>) {
    let base = lib.join(format!("{}.olean", module.replace('.', "/")));
    let read = |p: PathBuf| std::fs::read(&p).unwrap_or_else(|e| panic!("read {p:?}: {e}"));
    let exported = read(base.clone());
    match level {
        Level::Exported => {
            header_name_arrays(&OleanView::parse(&exported).expect("parse exported"))
        }
        Level::Private => {
            let server = read(base.with_extension("olean.server"));
            let private = read(base.with_extension("olean.private"));
            header_name_arrays(
                &OleanView::parse_with_dependencies(&private, &[&exported, &server])
                    .expect("parse private"),
            )
        }
    }
}

/// `extraConstNames` overlaps `constNames`, and the overlap is exactly the
/// `.splitter` names — which the header cell above cannot see, because it
/// compares the two arrays only by LENGTH.
///
/// That cell asserts `extraConstNames != constants` and reads the result as
/// "a DIFFERENT population". Two unequal cardinalities are compatible with
/// total overlap, so what is established there is much weaker than what it
/// says. The names were never decoded, though the decoder has offered
/// `extra_const_names` all along.
///
/// The upstream doc-comment calls these "auxiliary declarations that are NOT in
/// the mapping `constants`", and taking that literally would have produced a
/// disjointness assertion that is FALSE at the pin. Measured:
///
///   exported level: disjoint, all four modules, and no `.splitter` occurs
///   private level:  the intersection is exactly the `.splitter` subset of
///                   `extraConstNames`, in both directions — every overlapping
///                   name ends in `.splitter`, and every `.splitter` in the
///                   extra array is also declared
///
/// So the documented property is about the environment's mapping, not about the
/// module header, and the distinction only becomes visible once the arrays are
/// compared as sets. Corroboration beyond what this cell walks: over all 600
/// `Init` modules at private level there are 29,050 extra names, 514 of them
/// overlapping across 141 modules, and every single one is a `.splitter`. That
/// sweep is provenance for the shape law, not something asserted here — this
/// cell checks the four modules it names.
///
/// One more array law falls out and is worth having: `extraConstNames` carries
/// no duplicate of its own, at either level, in any module walked.
#[test]
fn extra_const_names_overlap_declared_names_exactly_at_the_splitters() {
    let lib = lib_or_skip!();

    let mut overlapping_total = 0usize;
    let mut splitters_total = 0usize;
    for (module, expect_exported, expect_private, expect_overlap) in EXTRA_CONST_NAME_ROWS {
        for level in [Level::Exported, Level::Private] {
            let (declared, extra) = header_names(&lib, module, level);
            let label = match level {
                Level::Exported => "exported",
                Level::Private => "private",
            };
            let declared_set: BTreeSet<&String> = declared.iter().collect();
            let extra_set: BTreeSet<&String> = extra.iter().collect();
            assert_eq!(
                extra_set.len(),
                extra.len(),
                "{module} [{label}]: extraConstNames must not repeat a name"
            );
            assert_eq!(
                extra.len(),
                match level {
                    Level::Exported => *expect_exported,
                    Level::Private => *expect_private,
                },
                "{module} [{label}]: extraConstNames population"
            );

            let overlap: BTreeSet<&&String> = extra_set.intersection(&declared_set).collect();
            let splitters: BTreeSet<&&String> = extra_set
                .iter()
                .filter(|name| name.ends_with(".splitter"))
                .collect();
            // The law, in both directions: overlapping IS being a splitter.
            assert_eq!(
                overlap, splitters,
                "{module} [{label}]: the overlap between the two header arrays is exactly the \
                 splitters"
            );
            match level {
                Level::Exported => assert!(
                    overlap.is_empty(),
                    "{module}: the exported header carries no splitter, so its arrays are \
                     disjoint; got {overlap:?}"
                ),
                Level::Private => {
                    assert_eq!(
                        overlap.len(),
                        *expect_overlap,
                        "{module}: private overlap count"
                    );
                    overlapping_total += overlap.len();
                    splitters_total += splitters.len();
                }
            }
        }
    }

    // Anti-vacuity, and it needs both sides. A module set with no overlap at all
    // would satisfy the biconditional trivially, and so would one where every
    // extra name were a splitter.
    assert_eq!(
        (overlapping_total, splitters_total),
        (35, 35),
        "the overlapping population must be real"
    );
    let (_, prelude_extra) = header_names(&lib, "Init.Prelude", Level::Private);
    assert!(
        prelude_extra
            .iter()
            .all(|name| !name.ends_with(".splitter")),
        "Init.Prelude carries extra names and none is a splitter, so the empty overlap there is \
         a consequence of the law rather than an absence of data"
    );
}

/// The two `Init` modules whose import array repeats a row IDENTICALLY.
const IDENTICAL_IMPORT_ROWS: &[&str] = &["Init.Data.Nat", "Init.Data.String"];

/// Every `Init` module in the pin, as dotted names.
fn init_modules(lib: &Path) -> Vec<String> {
    let mut out = Vec::new();
    let mut stack = vec![lib.join("Init")];
    while let Some(dir) = stack.pop() {
        let entries = std::fs::read_dir(&dir).unwrap_or_else(|e| panic!("read_dir {dir:?}: {e}"));
        for entry in entries {
            let path = entry.expect("dir entry").path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|ext| ext == "olean") {
                let rel = path
                    .strip_prefix(lib)
                    .expect("under lib")
                    .with_extension("");
                out.push(rel.to_string_lossy().replace('/', "."));
            }
        }
    }
    out.sort();
    out
}

/// An import row is NOT keyed by its module name, and only barely by the whole
/// row — which matters because keying it by name is the natural thing to do and
/// silently discards `importAll`.
///
/// The import cell above reads one module's seven rows and settles what
/// licenses the cross-module private reference. It leaves the array's own
/// shape unasserted, and `ModuleImport`'s doc-comment makes a claim about that
/// shape — "array order and duplicate rows are observable and are therefore
/// preserved" — that nothing here tested.
///
/// Measured over all 600 `Init` modules, 3,153 import edges, and the counts are
/// identical at both levels:
///
///   102 modules import the same module TWICE, so the module name is not a key
///   100 of those repeat with DIFFERENT flags — the same module imported once
///     plainly and once as `meta`, or once plainly and once as `import all`
///   2 repeat a row identically, and they are named above
///
/// So neither candidate key holds. A decoder or environment builder that keys
/// imports by module name drops 100 flag-distinct edges across `Init` alone,
/// and among what it drops are `importAll` edges — precisely the flag that
/// licenses reading a private part, which is the mechanism this whole bead
/// turns on. That is the non-injective-projection shape this repository has
/// caught before: a projection used as an identity without anyone checking that
/// it is injective.
///
/// One flag relation falls out and is asserted ONE-WAY, because the converse is
/// false and measured false: all 226 `importAll` edges have `isExported` clear,
/// while 1,379 edges have `isExported` clear without `importAll`. Implication,
/// not equivalence.
#[test]
fn import_rows_are_keyed_by_neither_the_module_name_nor_reliably_the_row() {
    let lib = lib_or_skip!();
    let modules = init_modules(&lib);
    assert_eq!(modules.len(), 600, "the Init module census must be reached");
    let present: BTreeSet<&String> = modules.iter().collect();

    let mut edges = 0usize;
    let mut repeated_name: Vec<&String> = Vec::new();
    let mut repeated_row: Vec<&String> = Vec::new();
    let mut flag_distinct = 0usize;
    let mut import_all = 0usize;
    let mut import_all_exported = 0usize;
    let mut unexported_without_import_all = 0usize;
    let mut combinations: BTreeSet<(bool, bool, bool)> = BTreeSet::new();
    let mut unresolved: Vec<String> = Vec::new();

    for module in &modules {
        let view = module_view(&lib, module, Level::Exported);
        edges += view.imports.len();

        let mut names: BTreeSet<String> = BTreeSet::new();
        let mut rows: BTreeSet<(String, bool, bool, bool)> = BTreeSet::new();
        let mut duplicate_name = false;
        let mut duplicate_row = false;
        for import in &view.imports {
            let name = import.module.to_display_string();
            let row = (
                name.clone(),
                import.import_all,
                import.is_exported,
                import.is_meta,
            );
            combinations.insert((import.import_all, import.is_exported, import.is_meta));
            if import.import_all {
                import_all += 1;
                if import.is_exported {
                    import_all_exported += 1;
                }
            } else if !import.is_exported {
                unexported_without_import_all += 1;
            }
            if !present.contains(&name) {
                unresolved.push(format!("{module} -> {name}"));
            }
            duplicate_name |= !names.insert(name);
            duplicate_row |= !rows.insert(row);
        }
        if duplicate_name {
            repeated_name.push(module);
            if duplicate_row {
                repeated_row.push(module);
            } else {
                flag_distinct += 1;
            }
        }
    }

    assert!(
        unresolved.is_empty(),
        "every import names a module the pin supplies; these do not: {:?}",
        &unresolved[..unresolved.len().min(8)]
    );
    assert_eq!(edges, 3_153, "the import edge census must be complete");
    assert_eq!(
        (repeated_name.len(), flag_distinct),
        (102, 100),
        "the module name is not a key, and almost every repeat is flag-distinct rather than a \
         true duplicate"
    );
    assert_eq!(
        repeated_row, IDENTICAL_IMPORT_ROWS,
        "the whole row is not a key either, and these two are why"
    );

    // The flag relation, one-way. Both sides are asserted so that a future
    // artifact turning it into an equivalence fails here rather than passing.
    assert_eq!(
        (import_all, import_all_exported),
        (226, 0),
        "importAll implies isExported is clear"
    );
    assert!(
        unexported_without_import_all > 1_000,
        "the converse must stay false: {unexported_without_import_all} edges are unexported \
         without importAll"
    );
    assert_eq!(
        combinations.len(),
        5,
        "five of the eight flag combinations occur at the pin, so no flag decodes to a constant"
    );
}

/// `(module, names carrying a num component, the index it sits at)`.
const PRIVATE_NAME_ROWS: &[(&str, usize, usize)] = &[
    ("Init.Prelude", 113, 3),
    ("Init.Meta.Defs", 156, 4),
    ("Init.Data.List.Basic", 73, 5),
];

/// One stored name's components, root first, as owned values.
#[derive(Debug, PartialEq, Eq)]
enum Component {
    Str(String),
    Num(u64),
}

fn name_components(name: &Name) -> (Vec<Component>, bool) {
    let mut out = Vec::new();
    let mut overflowed = false;
    let mut current = name.clone();
    while !current.is_anonymous() {
        overflowed |= current.component_overflowed();
        match current.leaf_view() {
            fln_core::name::LeafView::Str(text) => out.push(Component::Str(text.to_string())),
            fln_core::name::LeafView::Num(value) => out.push(Component::Num(value)),
            fln_core::name::LeafView::Anonymous => break,
        }
        current = current.parent();
    }
    out.reverse();
    (out, overflowed)
}

/// A `Name` is a tree of `str` and `num` components, and this file has read
/// every one of them through `to_display_string` — a projection that renders a
/// `num` as bare digits and therefore cannot be inverted.
///
/// That matters more here than it looks. Every cell in this file matches names
/// as strings: `_private.` prefixes, `.splitter` suffixes, `.rec` delegates,
/// `_impl` correspondences. All of it rests on the display string being a
/// faithful stand-in for the stored name, and nothing checked that it is. It is
/// the same shape as the import-row key: a projection used as an identity.
///
/// Measured, and the assumption holds — for a reason that is measured rather
/// than structural. Across the three modules named above, no `str` component
/// consists of digits, so no `str` component can collide with a `num` one, so
/// display strings are injective on each module's `constNames`. A single
/// declaration named with a digit-only string component would break that, and
/// nothing in the format forbids one. Both facts are asserted: the injectivity,
/// and the absence of collision material that explains it.
///
/// The rest is an exact biconditional, which is worth stating plainly after
/// three one-way results on this bead:
///
///   a name carries a `num` component IFF its first component is `_private`
///   there is exactly one such component, its value is always 0, and no
///     component ever overflows
///   it sits at index `1 + <components in the owning module name>` — 3 for
///     `Init.Prelude`, 4 for `Init.Meta.Defs`, 5 for `Init.Data.List.Basic`
///
/// So the private-name shape the earlier scope cell reads off a string is
/// actually stored structurally, and the num component's POSITION encodes the
/// owning module's own component count.
#[test]
fn private_names_are_the_only_ones_carrying_a_num_component() {
    let lib = lib_or_skip!();

    for (module, expect_private, expect_index) in PRIVATE_NAME_ROWS {
        let (infos, _) = decode_at(&lib, module, Level::Private);
        assert!(
            infos.len() > 500,
            "{module}: the declaration census must be reached, got {}",
            infos.len()
        );
        let module_components = module.split('.').count();

        let mut private = 0usize;
        let mut mismatched: Vec<String> = Vec::new();
        let mut numeric_strings: Vec<String> = Vec::new();
        let mut displays: BTreeSet<String> = BTreeSet::new();
        let mut total = 0usize;
        for info in &infos {
            let name = info.name();
            let display = name.to_display_string();
            total += 1;
            displays.insert(display.clone());

            let (components, overflowed) = name_components(name);
            assert!(
                !overflowed,
                "{module}: {display} carries a num component too large to store"
            );
            for component in &components {
                if let Component::Str(text) = component {
                    if !text.is_empty() && text.chars().all(|c| c.is_ascii_digit()) {
                        numeric_strings.push(display.clone());
                    }
                }
            }

            let scoped = components.first() == Some(&Component::Str("_private".to_owned()));
            let nums: Vec<usize> = components
                .iter()
                .enumerate()
                .filter_map(|(index, component)| {
                    matches!(component, Component::Num(_)).then_some(index)
                })
                .collect();
            if scoped != !nums.is_empty() {
                mismatched.push(display.clone());
                continue;
            }
            if !scoped {
                continue;
            }
            private += 1;
            assert_eq!(
                nums.len(),
                1,
                "{module}: {display} carries more than one num component"
            );
            assert_eq!(
                nums[0],
                module_components + 1,
                "{module}: {display} places its scope index after the module components"
            );
            assert_eq!(
                components[nums[0]],
                Component::Num(0),
                "{module}: {display} carries a scope index other than 0"
            );
        }

        assert!(
            mismatched.is_empty(),
            "{module}: carrying a num component and being `_private`-scoped are the same \
             property; these disagree: {:?}",
            &mismatched[..mismatched.len().min(8)]
        );
        assert_eq!(
            private, *expect_private,
            "{module}: the scoped population must be complete"
        );
        assert_eq!(
            *expect_index,
            module_components + 1,
            "{module}: the row's index must be the derived one, not an independent constant"
        );

        // Why the display projection is safe HERE, stated as the measured fact
        // it is: there is no collision material. And that it is in fact safe.
        assert!(
            numeric_strings.is_empty(),
            "{module}: a digit-only str component would render like a num one; these do: {:?}",
            &numeric_strings[..numeric_strings.len().min(8)]
        );
        assert_eq!(
            displays.len(),
            total,
            "{module}: display strings must be injective over the declarations"
        );
        assert!(
            private < total,
            "{module}: the scoped population must be a proper subset, got {private} of {total}"
        );
    }
}

/// The whole nested family, which shares one minor-premise count.
const NESTED_RECURSOR_FAMILY: &[&str] =
    &["Lean.Syntax.rec", "Lean.Syntax.rec_1", "Lean.Syntax.rec_2"];

/// ORDER and MULTIPLICITY in a recursor's rule list — what the block cell's
/// `BTreeSet` comparison necessarily discards.
///
/// The block-relations cell already compares a recursor's rule constructors
/// against its block's constructors, and finds them equal. It compares them as
/// SETS. A set comparison cannot see either of the two properties the kernel
/// actually depends on: a second rule for one constructor collapses into the
/// same set, and any permutation of the rules produces the same set. This cell
/// asserts only that delta; the set equality is not re-derived here.
///
/// The delta is on this bead's own failure class. Our kernel resolves a rule by
/// searching the list for the constructor's name rather than by indexing it, so
/// a duplicate rule is not an error — the search takes the first and the second
/// is unreachable, silently. And a missing rule does not fail to decode and does
/// not fail to resolve; the recursor simply never reduces, which is a
/// restrictive divergence of exactly the kind d17i collects.
///
/// Measured over `Init/Prelude` at private level, 129 recursors:
///
///   127 have `rules` equal to the concatenated `ctors` of their block IN
///     ORDER, and ZERO have the right constructors in the wrong order — so the
///     stronger sequence law holds wherever the set law does
///   0 have two rules for one constructor
///   the 2 departures are the nested auxiliaries the block cell already names,
///     whose rules are for `Array.mk` and `List.nil`/`List.cons`
///
/// `num_minors` agrees with the rule count for 126, and the three exceptions
/// are exactly the nested family: each of them stores `num_minors == 7` and
/// `num_motives == 3` — the totals for the whole family — while their own rule
/// lists partition those seven as 4 + 1 + 2. So `num_minors` is a property of
/// the block, not of the recursor, and that is only visible where a block holds
/// more than one recursor.
#[test]
fn a_recursors_rule_list_is_the_constructor_list_of_its_block() {
    let lib = lib_or_skip!();
    let infos = decode_prelude_private(&lib);

    let mut inductives: BTreeMap<String, &InductiveVal> = BTreeMap::new();
    let mut recursors: BTreeMap<String, &RecursorVal> = BTreeMap::new();
    for info in &infos {
        let name = info.name().to_display_string();
        match info {
            ConstantInfo::Induct(v) => drop(inductives.insert(name, v)),
            ConstantInfo::Rec(v) => drop(recursors.insert(name, v)),
            _ => {}
        }
    }
    assert_eq!(recursors.len(), 129, "the recursor census must be reached");

    let mut out_of_correspondence: Vec<&String> = Vec::new();
    let mut reordered: Vec<&String> = Vec::new();
    let mut duplicated: Vec<&String> = Vec::new();
    let mut minors_disagree: Vec<&String> = Vec::new();
    let mut rule_counts: BTreeMap<usize, usize> = BTreeMap::new();
    let mut nested_rules = 0usize;

    for (name, rec) in &recursors {
        let rules: Vec<String> = rec
            .rules
            .iter()
            .map(|rule| rule.ctor.to_display_string())
            .collect();
        *rule_counts.entry(rules.len()).or_default() += 1;

        let unique: BTreeSet<&String> = rules.iter().collect();
        if unique.len() != rules.len() {
            duplicated.push(name);
        }

        let mut expected: Vec<String> = Vec::new();
        for member in &rec.all {
            if let Some(induct) = inductives.get(&member.to_display_string()) {
                expected.extend(induct.ctors.iter().map(Name::to_display_string));
            }
        }
        if rules != expected {
            out_of_correspondence.push(name);
            // Distinguish a real reordering from a different constructor set:
            // the first would be a decode defect, the second is the nesting.
            let (mut a, mut b) = (rules.clone(), expected.clone());
            a.sort();
            b.sort();
            if a == b {
                reordered.push(name);
            }
        }
        if rec.num_minors as usize != rules.len() {
            minors_disagree.push(name);
        }
        if NESTED_RECURSOR_FAMILY.contains(&name.as_str()) {
            assert_eq!(
                (rec.num_minors, rec.num_motives),
                (7, 3),
                "{name}: the nested family shares one minor and motive count"
            );
            nested_rules += rules.len();
        }
    }

    assert!(
        duplicated.is_empty(),
        "the kernel resolves a rule by searching for the constructor's name, so a second rule \
         for one constructor is unreachable rather than an error; these carry one: {duplicated:?}"
    );
    assert!(
        reordered.is_empty(),
        "no recursor has the right constructors in the wrong order: {reordered:?}"
    );
    assert_eq!(
        out_of_correspondence, NESTED_AUXILIARY_RECURSORS,
        "only the nested auxiliaries depart from their block's constructor list"
    );
    assert_eq!(
        minors_disagree, NESTED_RECURSOR_FAMILY,
        "num_minors is a property of the block, so it disagrees with the rule count exactly \
         where a block holds more than one recursor"
    );
    assert_eq!(
        nested_rules, 7,
        "the family's three rule lists partition its seven minor premises"
    );

    // Non-vacuity: a decode returning a uniform rule list would have to hit
    // every one of these bucket sizes to pass.
    assert_eq!(
        (
            rule_counts.get(&0).copied().unwrap_or_default(),
            rule_counts.get(&1).copied().unwrap_or_default(),
            rule_counts.keys().copied().max().unwrap_or_default()
        ),
        (3, 108, 13),
        "the rule-count spread must be real, got {rule_counts:?}"
    );
}

/// The extension whose entry count is an independent witness of the module's
/// exported declaration count.
const EXPORTED_AXIOMS_EXTENSION: &str = "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt";

/// `(module, exported constNames, private constNames, witness entries)`.
const AXIOM_WITNESS_ROWS: &[(&str, usize, usize, Option<u64>)] = &[
    ("Init.Control", 0, 0, None),
    ("Init.Prelude", 2204, 2314, Some(2204)),
    ("Init.Meta.Defs", 379, 530, Some(379)),
    ("Init.Data.List.Basic", 791, 805, Some(791)),
    ("Init.Data.Array.Lemmas", 1018, 1297, Some(1018)),
];

/// `ExtensionBlock.entries` — the last unread field in the module header, and
/// it turns out to carry a SECOND, INDEPENDENT count of the exported
/// declarations.
///
/// The extension cell above maps every block to its `name` and compares the two
/// levels as name sets. `entries` is never read, so the size of what each block
/// holds has been invisible, and a duplicate block name would have collapsed
/// into the same set unnoticed.
///
/// Reading it produces a relation worth more than the field itself. The block
/// `exportedAxiomsExt` is written by `CollectAxioms`, a different part of the
/// pipeline from the one that fills `constNames`, and its entry count equals the
/// module's EXPORTED declaration count exactly — and stays at the exported
/// figure when the module is read at PRIVATE level, where `constNames` is
/// larger. That is the exported/private distinction this whole bead turns on,
/// corroborated from an unrelated array. If part selection were wrong again, the
/// constant array and this witness would disagree.
///
/// The presence rule is an exact biconditional, measured over all 600 `Init`
/// modules and recorded here as provenance rather than asserted: the block
/// occurs iff the module exports at least one declaration — 517 modules carry
/// it and every count matches with zero violations, 83 lack it and ALL 83 have
/// an empty exported constant array, and no module carries it with an empty
/// one. `Init.Control` is the zero-export row below, so both sides of the
/// biconditional are exercised by the cells that actually run.
///
/// Two smaller facts fall out and are asserted because the name-set comparison
/// cannot see either: no block name repeats within a module, and no block is
/// empty. A third — no shared block's entry count SHRINKS between the levels —
/// extends the "the private part adds and never removes" result from block
/// presence to block contents.
#[test]
fn the_axioms_extension_counts_exported_declarations_at_both_levels() {
    let lib = lib_or_skip!();

    for (module, exported_names, private_names, witness) in AXIOM_WITNESS_ROWS {
        let exported = module_view(&lib, module, Level::Exported);
        let private = module_view(&lib, module, Level::Private);
        assert_eq!(
            (exported.const_names.len(), private.const_names.len()),
            (*exported_names, *private_names),
            "{module}: the declaration counts this row is stated against"
        );

        for (label, view) in [("exported", &exported), ("private", &private)] {
            let names: BTreeSet<&str> = view
                .extensions
                .iter()
                .map(|block| block.name.as_str())
                .collect();
            assert_eq!(
                names.len(),
                view.extensions.len(),
                "{module} [{label}]: a block name must not repeat, which the name-set \
                 comparison elsewhere cannot see"
            );
            assert!(
                view.extensions.iter().all(|block| block.entries > 0),
                "{module} [{label}]: a stored extension block is never empty"
            );

            let found = view
                .extensions
                .iter()
                .find(|block| block.name == EXPORTED_AXIOMS_EXTENSION)
                .map(|block| block.entries);
            assert_eq!(
                found, *witness,
                "{module} [{label}]: the axioms witness is present exactly when the module \
                 exports a declaration, and counts them"
            );
        }

        // The witness is pinned to the EXPORTED count at both levels, so for a
        // module whose private array is larger it is a different number from
        // the one the private level would report. Without that gap the equality
        // would hold for an uninteresting reason.
        if let Some(entries) = witness {
            assert_eq!(*entries as usize, *exported_names);
            assert!(
                private_names > exported_names,
                "{module}: this row must discriminate — the private array has to be strictly \
                 larger for the witness to be saying anything"
            );
        }

        // Contents, not just presence: nothing a level shares with the exported
        // part ever holds fewer entries.
        let sizes: BTreeMap<&str, u64> = exported
            .extensions
            .iter()
            .map(|block| (block.name.as_str(), block.entries))
            .collect();
        let shrunk: Vec<&str> = private
            .extensions
            .iter()
            .filter(|block| {
                sizes
                    .get(block.name.as_str())
                    .is_some_and(|before| block.entries < *before)
            })
            .map(|block| block.name.as_str())
            .collect();
        assert!(
            shrunk.is_empty(),
            "{module}: the private part must not shrink an extension it shares: {shrunk:?}"
        );
    }
}

/// The extension blocks the SERVER part contributes over the exported one.
const SERVER_ONLY_EXTENSIONS: &[&str] = &[
    "Lean.declRangeExt",
    "Lean.docStringExt",
    "_private.Lean.DocString.Extension.0.Lean.inheritDocStringExt",
    "_private.Lean.DocString.Extension.0.Lean.moduleDocExt",
];

/// Read the middle part of the companion chain.
fn server_module_view(lib: &Path, module: &str) -> ModuleDataView {
    let base = lib.join(format!("{}.olean", module.replace('.', "/")));
    let read = |p: PathBuf| std::fs::read(&p).unwrap_or_else(|e| panic!("read {p:?}: {e}"));
    let exported = read(base.clone());
    let server = read(base.with_extension("olean.server"));
    OleanView::parse_with_dependencies(&server, &[&exported])
        .expect("parse server part")
        .module_data(WalkBudget::default())
        .expect("server module data")
}

/// The MIDDLE part of the companion chain, which nothing here had opened.
///
/// A module ships THREE parts and this file has read two. `.olean.server` is
/// handed to `parse_with_dependencies` as a byte buffer by every cell here and
/// then never examined, so what the middle of the chain contains has been an
/// open question on a bead whose entire repair was part SELECTION.
///
/// Measured over three modules, and the answer is uniform: the server part adds
/// no declarations at all.
///
///   `constNames` at server equals the exported array as a SEQUENCE, not merely
///     in length — 2,204 / 379 / 791, the same names in the same order
///   `extraConstNames` likewise, and the import array is identical at all three
///   the extension names NEST, exported ⊆ server ⊆ private, strictly at each
///     step — 56 < 60 < 62 for `Init/Prelude`
///   what the server adds is the same FOUR blocks in every module, and all four
///     are documentation extensions: `declRangeExt`, `docStringExt`,
///     `inheritDocStringExt`, `moduleDocExt`
///
/// So reading the server part instead of the private one would have recovered
/// ZERO of the declarations this bead is about. The private part is the only
/// one that adds any, which is the fact the part-selection repair rests on and
/// which nothing had checked from the middle part's own bytes.
///
/// This also DECOMPOSES a fact already recorded here. The extension cell lists
/// six blocks as private-only and calls them "the documentation and
/// compiler-cache extensions". That is true against the exported part, but it
/// attributes all six to the private level; four of the six are contributed by
/// the SERVER part, and only the two compiler-cache ones are genuinely private.
/// Both statements are consistent — the parts nest — but only this one says
/// which part supplies what.
#[test]
fn the_server_part_adds_documentation_extensions_and_no_declarations() {
    let lib = lib_or_skip!();

    for module in ["Init.Prelude", "Init.Meta.Defs", "Init.Data.List.Basic"] {
        let exported = module_view(&lib, module, Level::Exported);
        let server = server_module_view(&lib, module);
        let private = module_view(&lib, module, Level::Private);

        assert_eq!(
            server.const_names, exported.const_names,
            "{module}: the server part carries the exported constant array unchanged, name for \
             name and in order"
        );
        assert_eq!(
            (server.constants, server.extra_const_names),
            (exported.constants, exported.extra_const_names),
            "{module}: and the same auxiliary array"
        );
        assert_eq!(
            server.imports, exported.imports,
            "{module}: the import array is a property of the module, not of the part"
        );
        assert!(
            private.const_names.len() > exported.const_names.len(),
            "{module}: the private part is the only one that adds declarations, so it must be \
             the only one that grows"
        );

        let names = |view: &ModuleDataView| -> BTreeSet<String> {
            view.extensions
                .iter()
                .map(|block| block.name.clone())
                .collect()
        };
        let (exported_names, server_names, private_names) =
            (names(&exported), names(&server), names(&private));
        assert!(
            exported_names.is_subset(&server_names) && server_names.is_subset(&private_names),
            "{module}: the three parts' extension tables must nest"
        );
        assert!(
            exported_names.len() < server_names.len() && server_names.len() < private_names.len(),
            "{module}: and each step must actually add something ({} < {} < {})",
            exported_names.len(),
            server_names.len(),
            private_names.len()
        );

        let added: Vec<&String> = server_names.difference(&exported_names).collect();
        assert_eq!(
            added, SERVER_ONLY_EXTENSIONS,
            "{module}: the server part contributes exactly the documentation extensions"
        );
        assert!(
            private_names
                .difference(&server_names)
                .all(|name| !SERVER_ONLY_EXTENSIONS.contains(&name.as_str())),
            "{module}: nothing the server supplies may be counted again as a private addition"
        );
    }
}

/// `(module, shared declarations, kind changes, Axiom→Defn, Axiom→Thm,
/// Axiom→Opaque)`.
const LEVEL_TRANSITION_ROWS: &[(&str, usize, usize, usize, usize, usize)] = &[
    ("Init.Prelude", 2204, 246, 86, 148, 12),
    ("Init.Meta.Defs", 379, 197, 165, 16, 16),
    ("Init.Data.List.Basic", 791, 228, 20, 208, 0),
];

/// Changing which part you read cannot change what a declaration MEANS — the
/// soundness content of the part-selection repair, never asserted.
///
/// The kind cell above establishes that the private read does not rewrite kinds
/// wholesale and that no name is lost. Both are about the NAME set and the kind
/// tag. Neither says anything about the declaration's TYPE, and the type is the
/// whole of what a declaration asserts. A part selection that silently altered
/// types would satisfy every cell in this file and would be a soundness defect
/// rather than a restrictive one — the opposite direction from everything else
/// d17i collects, and the direction that actually matters.
///
/// Measured over three modules, 3,374 declarations present in both parts:
///
///   ZERO have a different `type_` — compared structurally, not by hash
///   ZERO have different `level_params`
///   671 change kind, and EVERY ONE of them is from `Axiom`. Not one
///     declaration changes between two kinds that both carry a value
///
/// So the exported part postulates and the private part supplies, and that is
/// the only thing that ever differs. `Axiom → Defn`, `Axiom → Thm` and
/// `Axiom → Opaque` all occur, in proportions that differ sharply per module —
/// `Init.Data.List.Basic` has 208 theorems restored and no opaques at all,
/// while `Init.Meta.Defs` is mostly definitions. The zero in that row is
/// asserted as a zero, so a decode that started producing opaques there fails.
#[test]
fn reading_the_private_part_changes_bodies_and_never_types() {
    let lib = lib_or_skip!();

    for (module, shared_count, changed_count, to_defn, to_thm, to_opaque) in LEVEL_TRANSITION_ROWS {
        let (exported, _) = decode_at(&lib, module, Level::Exported);
        let (private, _) = decode_at(&lib, module, Level::Private);

        let private_by_name: BTreeMap<String, &ConstantInfo> = private
            .iter()
            .map(|info| (info.name().to_display_string(), info))
            .collect();

        let mut shared = 0usize;
        let mut retyped: Vec<String> = Vec::new();
        let mut relevelled: Vec<String> = Vec::new();
        let mut transitions: BTreeMap<(&str, &str), usize> = BTreeMap::new();
        let mut not_from_axiom: Vec<(String, &str, &str)> = Vec::new();
        for before in &exported {
            let name = before.name().to_display_string();
            let Some(after) = private_by_name.get(&name) else {
                continue;
            };
            shared += 1;

            if before.constant_val().type_ != after.constant_val().type_ {
                retyped.push(name.clone());
            }
            if before.constant_val().level_params != after.constant_val().level_params {
                relevelled.push(name.clone());
            }
            let (from, to) = (kind_of(before), kind_of(after));
            if from != to {
                *transitions.entry((from, to)).or_default() += 1;
                if from != "Axiom" {
                    not_from_axiom.push((name, from, to));
                }
            }
        }

        assert!(
            retyped.is_empty(),
            "{module}: the private part must not change a declaration's type; these differ: {:?}",
            &retyped[..retyped.len().min(8)]
        );
        assert!(
            relevelled.is_empty(),
            "{module}: nor its universe parameters: {:?}",
            &relevelled[..relevelled.len().min(8)]
        );
        assert!(
            not_from_axiom.is_empty(),
            "{module}: every kind change is a postulate being supplied, so nothing may change \
             between two kinds that both carry a value: {not_from_axiom:?}"
        );

        assert_eq!(shared, *shared_count, "{module}: shared declaration census");
        let count = |to: &str| transitions.get(&("Axiom", to)).copied().unwrap_or_default();
        assert_eq!(
            (
                transitions.values().sum::<usize>(),
                count("Defn"),
                count("Thm"),
                count("Opaque")
            ),
            (*changed_count, *to_defn, *to_thm, *to_opaque),
            "{module}: the transition census, including the zeros"
        );
        // Non-vacuity: the comparison must be against a real population, and
        // the unchanged majority is what makes "zero retyped" meaningful rather
        // than a consequence of nothing being shared.
        assert!(
            *changed_count < shared,
            "{module}: most shared declarations keep their kind, so the type comparison runs \
             over declarations that did NOT change as well"
        );
    }
}

/// The import graph over `Init` is closed, acyclic, and has exactly ONE root —
/// which is the premise the reference-closure cell rests on and never
/// established.
///
/// The closure cell computes `Init/Prelude`'s reference closure precisely
/// because that module imports nothing, and the import cell asserts it imports
/// nothing. Neither asks whether it is the ONLY such module. It is, and that
/// changes what the closure result means: "the import-free root module" is a
/// definite description over the pin rather than a property `Init.Prelude`
/// happens to share with others, so the closure is not a sample of a class — it
/// is the only place the question can be asked without an import closure.
///
/// Measured over all 600 `Init` modules and their 3,153 import edges:
///
///   ZERO edges name a module outside `Init`, so the graph below is the whole
///     graph and not a subgraph whose acyclicity would prove less
///   exactly ONE module imports nothing, and it is `Init.Prelude`
///   no module imports itself
///   there is no cycle
///
/// Acyclicity is checked by an explicit three-colour DFS rather than by
/// attempting a topological sort, because a sort that silently dropped
/// unreachable nodes would report success over the part it managed to order.
/// Non-vacuity: 17 modules are imported by nobody and the most-imported reaches
/// 113, so this is neither a chain nor a star.
#[test]
fn the_init_import_graph_is_closed_acyclic_and_rooted_at_prelude() {
    let lib = lib_or_skip!();
    let modules = init_modules(&lib);
    assert_eq!(modules.len(), 600, "the Init module census must be reached");

    let index: BTreeMap<&str, usize> = modules
        .iter()
        .enumerate()
        .map(|(i, name)| (name.as_str(), i))
        .collect();
    let mut graph: Vec<Vec<usize>> = vec![Vec::new(); modules.len()];
    let mut in_degree = vec![0usize; modules.len()];
    let mut edges = 0usize;
    let mut escaping: Vec<String> = Vec::new();
    let mut roots: Vec<&String> = Vec::new();
    let mut self_importing: Vec<&String> = Vec::new();

    for (i, module) in modules.iter().enumerate() {
        let view = module_view(&lib, module, Level::Exported);
        if view.imports.is_empty() {
            roots.push(module);
        }
        for import in &view.imports {
            edges += 1;
            let name = import.module.to_display_string();
            match index.get(name.as_str()) {
                Some(target) => {
                    if *target == i {
                        self_importing.push(module);
                    }
                    graph[i].push(*target);
                    in_degree[*target] += 1;
                }
                None => escaping.push(format!("{module} -> {name}")),
            }
        }
    }

    assert!(
        escaping.is_empty(),
        "no Init module imports outside Init, so the graph is closed: {:?}",
        &escaping[..escaping.len().min(8)]
    );
    assert_eq!(edges, 3_153, "the import edge census must be complete");
    assert_eq!(
        roots,
        vec!["Init.Prelude"],
        "exactly one module imports nothing, and the closure cell's root is that module"
    );
    assert!(
        self_importing.is_empty(),
        "no module imports itself: {self_importing:?}"
    );

    // Three-colour DFS: 0 unvisited, 1 on the current path, 2 finished.
    let mut colour = vec![0u8; modules.len()];
    let mut cycles: Vec<String> = Vec::new();
    for start in 0..modules.len() {
        if colour[start] != 0 {
            continue;
        }
        colour[start] = 1;
        let mut stack: Vec<(usize, usize)> = vec![(start, 0)];
        while let Some(&mut (node, ref mut cursor)) = stack.last_mut() {
            let Some(next) = graph[node].get(*cursor).copied() else {
                colour[node] = 2;
                stack.pop();
                continue;
            };
            *cursor += 1;
            match colour[next] {
                1 => cycles.push(format!("{} -> {}", modules[node], modules[next])),
                0 => {
                    colour[next] = 1;
                    stack.push((next, 0));
                }
                _ => {}
            }
        }
    }
    assert!(
        cycles.is_empty(),
        "the import graph must be acyclic: {:?}",
        &cycles[..cycles.len().min(8)]
    );
    assert!(
        colour.iter().all(|c| *c == 2),
        "every module must be visited, or the acyclicity result covers only part of the graph"
    );

    let sinks = in_degree.iter().filter(|d| **d == 0).count();
    let busiest = in_degree.iter().copied().max().unwrap_or_default();
    assert_eq!(
        (sinks, busiest),
        (17, 113),
        "the graph must be a real DAG rather than a chain or a star"
    );
}

/// The module census is keyed by a projection, and the projection is injective
/// — the identity law underneath both import cells.
///
/// `init_modules` turns a file path into a module name by stripping the final
/// extension and replacing `/` with `.`. Two committed cells resolve every
/// import edge by looking a name up in the set that projection produces: the
/// import-row cell checks each edge names a module the pin supplies, and the
/// graph cell builds its adjacency from a name-to-index map. Neither checks
/// that the projection is a KEY.
///
/// It would fail on one input. A file named `Init/Foo.Bar.olean` projects onto
/// `Init.Foo.Bar` and collides with `Init/Foo/Bar.olean`, because stripping the
/// final extension leaves the interior dot in place. A collision does not raise
/// anything: the name-to-index map silently keeps one member, edges to the other
/// resolve to the WRONG module, and the acyclicity result would then be about a
/// graph that is not the pin's. This is the shape this repository has caught
/// repeatedly — a projection used as an identity with nobody checking that it
/// is injective.
///
/// Measured, and it holds for a reason that is measured rather than structural:
///
///   600 files project onto 600 distinct names, and 2,433 across the whole
///     library project onto 2,433
///   NO `.olean` basename contains a dot, which is the only collision material
///     there is. Nothing in the layout forbids one
///   every census module has both companion parts on disk, so `Level::Private`
///     is defined for every member — a premise several cells rest on and none
///     of them states
#[test]
fn the_module_census_is_keyed_by_an_injective_path_projection() {
    let lib = lib_or_skip!();
    let modules = init_modules(&lib);
    assert_eq!(modules.len(), 600, "the Init module census must be reached");

    let distinct: BTreeSet<&String> = modules.iter().collect();
    assert_eq!(
        distinct.len(),
        modules.len(),
        "the path projection must be injective, or a lookup keyed on it silently resolves an \
         edge to the wrong module"
    );

    // The collision material, counted directly from the filesystem rather than
    // from the projected names — a duplicate would have already been lost by
    // the time the names exist.
    let mut files = 0usize;
    let mut dotted: Vec<String> = Vec::new();
    let mut stack = vec![lib.join("Init")];
    while let Some(dir) = stack.pop() {
        let entries = std::fs::read_dir(&dir).unwrap_or_else(|e| panic!("read_dir {dir:?}: {e}"));
        for entry in entries {
            let path = entry.expect("dir entry").path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|ext| ext == "olean") {
                files += 1;
                let stem = path
                    .file_stem()
                    .expect("a file has a stem")
                    .to_string_lossy()
                    .into_owned();
                if stem.contains('.') {
                    dotted.push(stem);
                }
            }
        }
    }
    assert_eq!(
        files,
        modules.len(),
        "the walk and the census must see the same files"
    );
    assert!(
        dotted.is_empty(),
        "a dot inside a basename is the one input that breaks the projection; these carry \
         one: {dotted:?}"
    );

    // Every member is readable at both levels, which the cells that decode at
    // `Level::Private` assume without saying.
    let mut incomplete: Vec<String> = Vec::new();
    for module in &modules {
        let base = lib.join(format!("{}.olean", module.replace('.', "/")));
        for part in ["olean.server", "olean.private"] {
            if !base.with_extension(part).is_file() {
                incomplete.push(format!("{module}.{part}"));
            }
        }
    }
    assert!(
        incomplete.is_empty(),
        "every census module must carry a complete companion chain: {:?}",
        &incomplete[..incomplete.len().min(8)]
    );

    // Non-vacuity: the projection must actually be exercised on nested paths,
    // not merely on files sitting at the top of the tree.
    let deepest = modules
        .iter()
        .map(|module| module.split('.').count())
        .max()
        .unwrap_or_default();
    assert!(
        deepest >= 5,
        "the census must contain deeply nested modules for the separator replacement to mean \
         anything, deepest is {deepest}"
    );
}

/// The two library modules that carry no companion parts at all.
const MODULES_WITHOUT_COMPANIONS: &[&str] = &["LeanChecker.olean", "Leanc.olean"];

/// Every `.olean` file under a root, split by which part of the chain it is.
#[derive(Default)]
struct ChainCensus {
    exported: BTreeSet<String>,
    server: BTreeSet<String>,
    private: BTreeSet<String>,
    unknown: Vec<String>,
}

fn chain_census(lib: &Path, root: &Path) -> ChainCensus {
    let mut out = ChainCensus::default();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let entries = std::fs::read_dir(&dir).unwrap_or_else(|e| panic!("read_dir {dir:?}: {e}"));
        for entry in entries {
            let path = entry.expect("dir entry").path();
            if path.is_dir() {
                stack.push(path);
                continue;
            }
            let relative = path
                .strip_prefix(lib)
                .expect("under lib")
                .to_string_lossy()
                .into_owned();
            if let Some(base) = relative.strip_suffix(".server") {
                if base.ends_with(".olean") {
                    out.server.insert(base.to_owned());
                    continue;
                }
            }
            if let Some(base) = relative.strip_suffix(".private") {
                if base.ends_with(".olean") {
                    out.private.insert(base.to_owned());
                    continue;
                }
            }
            if relative.ends_with(".olean") {
                out.exported.insert(relative);
            } else if relative.contains(".olean") {
                out.unknown.push(relative);
            }
        }
    }
    out
}

/// Every companion file on disk belongs to a module, the chain has exactly
/// THREE parts, and the completeness premise is total over `Init` and not over
/// the library.
///
/// The census cell asserts the forward direction — every census module has both
/// companions — by walking the census and stating the filesystem. That is a
/// one-way containment. The reverse was never checked, and it is the direction
/// that mirrors this bead's original defect: an orphan `.olean.private` with no
/// base `.olean` is a part that EXISTS and can never be read, because
/// `parse_with_dependencies` is given the exported part as its region. d17i was
/// a part that existed and was not read; this is the shape where nothing could
/// read it at all.
///
/// Counted from a directory walk rather than from the census, so a name the
/// projection would have collapsed is still counted here:
///
///   `Init` is a three-way bijection — 600 exported, 600 server, 600 private,
///     with ZERO orphans in either companion and zero bases missing one
///   the whole library has 2,433 exported and 2,431 of each companion, still
///     with zero orphans, and exactly TWO bases carry no companion at all:
///     `LeanChecker` and `Leanc`
///   NO file carries any other `.olean`-bearing suffix, so the chain is exactly
///     three parts. A fourth would be invisible to every cell in this file,
///     since all of them name the three they know
///
/// The two exceptions are why the premise is stated over `Init` and must not be
/// generalised: `Level::Private` is total over the census this file uses and is
/// NOT total over the library. A cell that widened its scope and kept the
/// premise would fail on those two, which is the correct outcome and worth
/// having recorded before someone widens one.
#[test]
fn companion_files_belong_to_modules_and_the_chain_has_exactly_three_parts() {
    let lib = lib_or_skip!();

    let init = chain_census(&lib, &lib.join("Init"));
    assert_eq!(
        (
            init.exported.len(),
            init.server.len(),
            init.private.len(),
            init.unknown.len()
        ),
        (600, 600, 600, 0),
        "the Init chain census"
    );
    for (label, part) in [("server", &init.server), ("private", &init.private)] {
        assert_eq!(
            part, &init.exported,
            "Init: the .{label} files and the .olean files must be the same set, in both \
             directions"
        );
    }

    let all = chain_census(&lib, &lib);
    assert_eq!(
        (
            all.exported.len(),
            all.server.len(),
            all.private.len(),
            all.unknown.len()
        ),
        (2433, 2431, 2431, 0),
        "the library chain census"
    );
    assert!(
        all.exported.len() > init.exported.len(),
        "the library walk must be strictly wider than the Init walk, or the exception below \
         is asserted over the same files that just satisfied the bijection"
    );

    for (label, part) in [("server", &all.server), ("private", &all.private)] {
        let orphans: Vec<&String> = part.difference(&all.exported).collect();
        assert!(
            orphans.is_empty(),
            "a .{label} file with no .olean beside it can never be read: {orphans:?}"
        );
        let missing: Vec<&String> = all.exported.difference(part).collect();
        assert_eq!(
            missing, MODULES_WITHOUT_COMPANIONS,
            "exactly two library modules carry no .{label}, so the completeness premise is \
             total over Init and NOT over the library"
        );
    }
}

/// `is_module` PREDICTS the companion chain — the exceptions the chain cell
/// names are derived from a stored flag, not carved out by hand.
///
/// The import cell reads `is_module` at two modules, finds it true at both
/// levels, and calls it "the premise of the entire companion-chain repair — a
/// non-module olean has no `.private` part to read". That sentence is an
/// implication whose interesting direction is `is_module == false`, and both of
/// its samples have it TRUE. The claim is stated in prose and exercised nowhere.
///
/// The chain cell, for its part, names `LeanChecker` and `Leanc` as the two
/// library modules carrying no companions, and gives no reason. The reason is a
/// stored byte, and the two facts are the same fact:
///
///   library-wide, 2,433 oleans carry `is_module` true 2,431 times and false
///     twice, and the false set is EXACTLY the set with no companion parts —
///     equal in both directions
///   all 600 `Init` census modules carry it true, and all 600 have companions
///
/// So the carve-out is derived rather than hand-listed. Both names below are
/// discovered from the filesystem walk rather than written into the assertion,
/// which is the difference between checking the property and re-stating the
/// list: a third non-module olean appearing in the pin would be picked up here
/// instead of failing an equality against two hardcoded strings.
///
/// The library-wide count is provenance for the biconditional; what this cell
/// walks is the 600 census modules plus whatever the filesystem says lacks a
/// companion. A library module with `is_module` false that DID carry companions
/// is the one case outside that scope, and the sweep found none.
#[test]
fn the_is_module_flag_predicts_which_oleans_have_companions() {
    let lib = lib_or_skip!();

    // Derived, not listed: whatever the filesystem says has no private part.
    let all = chain_census(&lib, &lib);
    let without: Vec<String> = all
        .exported
        .difference(&all.private)
        .map(|path| {
            path.strip_suffix(".olean")
                .expect("an exported part ends in .olean")
                .replace('/', ".")
        })
        .collect();
    assert!(
        !without.is_empty() && without.len() < all.exported.len(),
        "the no-companion population must be a real, proper subset, got {} of {}",
        without.len(),
        all.exported.len()
    );

    for module in &without {
        assert!(
            !module_view(&lib, module, Level::Exported).is_module,
            "{module} carries no companion parts, so it must not be flagged a module"
        );
    }

    let modules = init_modules(&lib);
    assert_eq!(modules.len(), 600, "the Init module census must be reached");
    let mut not_flagged: Vec<&String> = Vec::new();
    for module in &modules {
        if !module_view(&lib, module, Level::Exported).is_module {
            not_flagged.push(module);
        }
    }
    assert!(
        not_flagged.is_empty(),
        "every census module is flagged a module, which is what makes Level::Private defined \
         for all of them: {not_flagged:?}"
    );

    // Non-vacuity, and it is the whole point: the flag must take BOTH values
    // over what this cell reads. The existing two-module cell cannot say this,
    // because both of its samples are true — an `is_module` that decoded to a
    // constant `true` would satisfy it and fail here.
    assert!(
        without.iter().all(|module| !modules.contains(module)),
        "the false population must sit outside the census, or the two assertions above are \
         about the same files"
    );
}

/// The file's two decode helpers are the same decoding, decoding is
/// deterministic, and both agree with the header count.
///
/// This file reads `Init/Prelude` at private level through two different
/// helpers. `decode_prelude_private` opens the three parts and decodes.
/// `decode_at` first parses the exported part standalone to read its imports,
/// then parses the chain and decodes. They are separate code paths — 31 cells
/// use the first and 12 use the second — and nothing checks they produce the
/// same thing. If they drifted, the file's claims would silently split into two
/// populations while every cell went on describing "Init/Prelude at private
/// level".
///
/// Three identities, none of them previously stated:
///
///   the two helpers agree element for element AND in order, so a cell may be
///     moved between them without changing what it asserts
///   decoding the same bytes twice through the same helper gives the same
///     result. The decoder caches names, levels and expressions in `HashMap`s,
///     and a `HashMap` iterated anywhere on the output path would leak its
///     order into the answer — a nondeterminism this project's own doctrine
///     rules out, and one that no single decode can reveal
///   the decoded count equals the `constants` field read from the header by
///     `module_view`, which is a different reader over the same bytes
///
/// Non-vacuity: the comparison runs over 2,314 declarations spanning all EIGHT
/// `ConstantInfo` kinds, so it is not agreement over a short or uniform list.
#[test]
fn the_two_decode_helpers_agree_and_decoding_is_deterministic() {
    let lib = lib_or_skip!();

    let direct = decode_prelude_private(&lib);
    let (routed, _) = decode_at(&lib, "Init.Prelude", Level::Private);
    assert_eq!(
        direct.len(),
        routed.len(),
        "the two helpers must decode the same number of declarations"
    );
    assert!(
        direct == routed,
        "the two helpers must produce the same declarations in the same order; first \
         disagreement at {:?}",
        direct
            .iter()
            .zip(&routed)
            .position(|(a, b)| a != b)
            .map(|index| direct[index].name().to_display_string())
    );

    let again = decode_prelude_private(&lib);
    assert!(
        direct == again,
        "decoding the same bytes twice must give the same answer, including order"
    );

    let header = module_view(&lib, "Init.Prelude", Level::Private);
    assert_eq!(
        direct.len() as u64,
        header.constants,
        "the decoded declarations must match the count the header reader reports"
    );

    let kinds: BTreeSet<&'static str> = direct.iter().map(kind_of).collect();
    assert_eq!(
        (direct.len(), kinds.len()),
        (2314, 8),
        "the agreement must be over the full census and every ConstantInfo kind, got {kinds:?}"
    );
}

/// The pinned toolchain, as the artifact identifies ITSELF rather than as the
/// path says.
const PIN_LEAN_VERSION: &str = "4.32.0";
const PIN_GITHASH: &str = "8c9756b28d64dab099da31a4c09229a9e6a2ef35";

/// One part's header identity: `(lean_version, githash, base_addr)`.
fn header_identity(path: &Path) -> (String, String, u64) {
    let bytes = std::fs::read(path).unwrap_or_else(|e| panic!("read {path:?}: {e}"));
    let view = OleanView::parse(&bytes).unwrap_or_else(|e| panic!("parse {path:?}: {e}"));
    let header = &view.header;
    (
        header.lean_version.clone(),
        header.githash.clone(),
        header.base_addr,
    )
}

/// The library this file measures identifies itself as the pin — from its own
/// bytes, not from the directory it was found in.
///
/// Every count in this file is stated against "the pin": 2,204 and 2,314
/// declarations, 600 modules, 3,153 import edges, 35,225 level nodes. All of it
/// rests on `reference_lib`, which returns `FLN_REFERENCE_LIB` when set and
/// checks only that the path is a DIRECTORY. Point that variable at a different
/// toolchain and every cell here goes on asserting the pin's numbers against
/// something else — failing with count mismatches that read as decode defects,
/// or, for a toolchain whose numbers happened to line up, passing while
/// describing the wrong artifact. Nothing established which toolchain was
/// actually opened.
///
/// The header answers it. Measured:
///
///   all 600 `Init` modules carry ONE header identity — `lean_version` 4.32.0
///     and githash `8c9756b2…`, and the whole 2,433-file library carries the
///     same one
///   the three parts of a chain share that identity and have THREE DISTINCT
///     base addresses, which is why the companion chain has to be pointer-linked
///     across regions rather than read as one file
///
/// The constancy is asserted because `region.rs` claims it in a comment —
/// `lean_version` and `githash` are "properties of the TOOLCHAIN, identical
/// across every module" — and nothing tested it. The distinct base addresses are
/// asserted because they are the mechanism this bead's repair depends on: three
/// parts, three regions, one pointer graph.
#[test]
fn the_library_under_test_identifies_itself_as_the_pinned_toolchain() {
    let lib = lib_or_skip!();

    let base = lib.join("Init/Prelude.olean");
    let mut addresses: BTreeSet<u64> = BTreeSet::new();
    for part in ["olean", "olean.server", "olean.private"] {
        let (version, githash, address) = header_identity(&base.with_extension(part));
        assert_eq!(
            (version.as_str(), githash.as_str()),
            (PIN_LEAN_VERSION, PIN_GITHASH),
            "Init/Prelude.{part}: the part must identify itself as the pin"
        );
        addresses.insert(address);
    }
    assert_eq!(
        addresses.len(),
        3,
        "the three parts occupy three distinct regions, which is why the chain is linked by \
         pointer rather than read as one file"
    );

    let modules = init_modules(&lib);
    assert_eq!(modules.len(), 600, "the Init module census must be reached");
    let mut identities: BTreeSet<(String, String)> = BTreeSet::new();
    for module in &modules {
        let path = lib.join(format!("{}.olean", module.replace('.', "/")));
        let (version, githash, _) = header_identity(&path);
        identities.insert((version, githash));
    }
    assert_eq!(
        identities.len(),
        1,
        "lean_version and githash are properties of the toolchain, so every module must agree; \
         got {identities:?}"
    );
    assert_eq!(
        identities.first().map(|(v, g)| (v.as_str(), g.as_str())),
        Some((PIN_LEAN_VERSION, PIN_GITHASH)),
        "and that one identity must be the pin the file's numbers were measured against"
    );
}

/// Multiply-declared names the recognised equation-compiler tails do not match.
///
/// Disclosed as a remainder rather than absorbed into the pattern. Their tails
/// — `fun_cases_unfolding` and `congr_eq_N` — come from the functional-induction
/// and congruence machinery, which is adjacent to the equation compiler but not
/// the same generator, and widening the tail list to swallow them would also
/// swallow a real collision between unrelated declarations. A fourth such name
/// appearing in the pin fails here, which is the point of listing them.
const MULTI_DECLARED_NOT_EQUATION_SHAPED: &[&str] = &[
    "String.utf8EncodeChar.fun_cases_unfolding",
    "_private.Init.Data.String.Slice.0.String.Slice.Pos.skipWhile.match_1.congr_eq_1",
    "_private.Init.Data.String.Slice.0.String.Slice.Pos.skipWhile.match_1.congr_eq_2",
];

/// The most-duplicated name at the pin, and every module that declares it.
const MOST_DUPLICATED_NAME: &str = "InvImage.eq_1";
const MOST_DUPLICATED_DECLARERS: &[&str] = &[
    "Init.Data.Iterators.Combinators.Monadic.Attach",
    "Init.Data.Iterators.Combinators.Monadic.Take",
    "Init.Data.Iterators.Consumers.Access",
    "Init.Data.Range.Polymorphic.RangeIterator",
    "Init.Data.Slice.Array.Iterator",
    "Init.Data.String.Iterate",
    "Init.Data.String.Pattern.Basic",
];

/// A declaration name does NOT identify a module — but it does identify a
/// declaration, which is what keeps an environment keyed by name well defined.
///
/// The scope cell proves, for ONE named declaration, that a `_private` prefix
/// names the privacy scope rather than the storing module, and lists two
/// modules that store it. One example establishes the exception exists; it says
/// nothing about how common it is, and nothing at all about the general
/// question underneath it — whether a name identifies a declaration across the
/// library.
///
/// Measured over all 600 `Init` modules at private level, 65,273 distinct
/// declared names:
///
///   92 names are declared by MORE THAN ONE module, up to SEVEN for
///     `InvImage.eq_1`. So the name is not a key for the pair (module,
///     declaration), and anything keying on it alone collapses those
///   89 of the 92 are equation-compiler auxiliaries by their tail — `eq_1` ×36,
///     `congr_simp` ×24, `eq_2` ×9, `eq_def` ×9, `induct_unfolding` ×6,
///     `eq_3` ×4, `eq_4` ×1 — which is the family this bead exists to recover.
///     THREE are not matched by those tails and are pinned by name below,
///     because a pattern widened to cover them would also cover a genuine
///     collision of unrelated declarations
///   16,189 declarations are `_private`-scoped, and 16,155 of them carry a
///     scope prefix equal to their declaring module. The 34 that differ are the
///     population behind the scope cell's single example
///
/// The duplication is benign, and that is the load-bearing half: the seven
/// declarations of `InvImage.eq_1` agree on KIND and on TYPE. The environment
/// the kernel builds is keyed by name, so a name declared twice with different
/// content would be either a conflict or a silent shadowing; measured, it is
/// neither. The census is taken from the header name arrays, and the agreement
/// is checked by decoding only the seven modules that carry the worst case,
/// because decoding 600 modules' declarations would cost far more than every
/// other cell in this file put together.
#[test]
fn a_name_identifies_a_declaration_but_not_the_module_that_declares_it() {
    let lib = lib_or_skip!();
    let modules = init_modules(&lib);
    assert_eq!(modules.len(), 600, "the Init module census must be reached");

    let mut declarers: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut scoped = 0usize;
    let mut scope_is_declarer = 0usize;
    for module in &modules {
        for name in module_view(&lib, module, Level::Private).const_names {
            if let Some(rest) = name.strip_prefix("_private.") {
                scoped += 1;
                let components: Vec<&str> = rest.split('.').collect();
                let boundary = components
                    .iter()
                    .position(|part| part.chars().all(|c| c.is_ascii_digit()));
                if let Some(index) = boundary {
                    if components[..index].join(".") == *module {
                        scope_is_declarer += 1;
                    }
                }
            }
            declarers.entry(name).or_default().push(module.clone());
        }
    }

    let duplicated: BTreeMap<&String, &Vec<String>> = declarers
        .iter()
        .filter(|(_, owners)| owners.len() > 1)
        .collect();
    assert_eq!(
        (declarers.len(), duplicated.len()),
        (65_273, 92),
        "the name census and the duplicated population"
    );
    assert_eq!(
        (scoped, scope_is_declarer),
        (16_189, 16_155),
        "the private-scope population, of which 34 are stored outside the module their scope \
         prefix names"
    );

    // Every duplicated name is an equation-compiler auxiliary, which is what
    // makes the duplication a regeneration rather than a collision of unrelated
    // declarations.
    let stray: Vec<&str> = duplicated
        .keys()
        .filter(|name| {
            !["eq_def", "congr_simp", "induct_unfolding"]
                .iter()
                .any(|tail| name.ends_with(tail))
                && !name
                    .rsplit('.')
                    .next()
                    .is_some_and(|tail| tail.starts_with("eq_"))
        })
        .map(|name| name.as_str())
        .collect();
    assert_eq!(
        stray, MULTI_DECLARED_NOT_EQUATION_SHAPED,
        "the multiply-declared names the recognised equation-compiler tails do NOT match are \
         these three and no others"
    );

    let worst = duplicated
        .get(&MOST_DUPLICATED_NAME.to_owned())
        .expect("the most-duplicated name is declared more than once");
    assert_eq!(
        worst.as_slice(),
        MOST_DUPLICATED_DECLARERS,
        "the worst case must be exactly these seven modules"
    );

    // The load-bearing half: those seven are the SAME declaration. A name
    // declared twice with different content would be a conflict or a silent
    // shadowing in an environment keyed by name.
    let mut shapes: Vec<(&'static str, Expr)> = Vec::new();
    for module in MOST_DUPLICATED_DECLARERS {
        let (infos, _) = decode_at(&lib, module, Level::Private);
        let found = infos
            .iter()
            .find(|info| info.name().to_display_string() == MOST_DUPLICATED_NAME)
            .unwrap_or_else(|| panic!("{module} declares {MOST_DUPLICATED_NAME}"));
        shapes.push((kind_of(found), found.constant_val().type_.clone()));
    }
    assert_eq!(shapes.len(), MOST_DUPLICATED_DECLARERS.len());
    let disagreeing: Vec<&str> = shapes
        .iter()
        .zip(MOST_DUPLICATED_DECLARERS)
        .filter(|((kind, type_), _)| *kind != shapes[0].0 || *type_ != shapes[0].1)
        .map(|(_, module)| *module)
        .collect();
    assert!(
        disagreeing.is_empty(),
        "all seven declarations of {MOST_DUPLICATED_NAME} must agree on kind and type; these \
         differ: {disagreeing:?}"
    );
}

/// What a multiply-declared name agrees on across its declaring modules — and
/// the one thing it does NOT.
///
/// The cell above establishes that 92 names are declared by more than one
/// module, and checks kind and type agreement for ONE of them, the seven-module
/// worst case. That leaves 91 names unchecked, on the grounds that decoding all
/// 600 modules would cost more than the rest of the file. It does not have to:
/// only 90 modules declare a duplicated name, ~18,600 declarations in total,
/// which is roughly what decoding `Init/Prelude` eight times costs and this
/// file already decodes it thirty-one times.
///
/// Measured over all 223 declaration sites:
///
///   every one of the 92 is a THEOREM. No definition is ever multiply declared,
///     and that is the precondition everything below depends on
///   kind, type and universe parameters agree in EVERY module, zero exceptions
///   values do NOT always agree — 11 of the 92 carry a different proof in
///     different modules
///
/// The tempting statement here is "all 92 agree", and it is false. What makes
/// the disagreement harmless is precisely that all 92 are theorems: the value
/// of a theorem is a proof, two proofs of the same proposition are
/// interchangeable under proof irrelevance, and the kernel never unfolds one to
/// decide a conversion it could not decide without it. Had even one of the 11
/// been a `Defn`, a differing value would change definitional unfolding and be
/// a real conflict rather than a benign regeneration.
///
/// So the count 11 is asserted as a NON-ZERO. A decode that lost the difference
/// — by returning a constant value, or by resolving the name once and reusing
/// it — would report perfect agreement and pass a cell that only checked for
/// disagreement in the fields that matter.
#[test]
fn multiply_declared_names_agree_on_everything_except_their_proofs() {
    let lib = lib_or_skip!();
    let modules = init_modules(&lib);
    assert_eq!(modules.len(), 600, "the Init module census must be reached");

    let mut declarers: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for module in &modules {
        for name in module_view(&lib, module, Level::Private).const_names {
            declarers.entry(name).or_default().push(module.clone());
        }
    }
    declarers.retain(|_, owners| owners.len() > 1);
    let involved: BTreeSet<&String> = declarers.values().flatten().collect();
    let sites: usize = declarers.values().map(Vec::len).sum();
    assert_eq!(
        (declarers.len(), sites, involved.len()),
        (92, 223, 90),
        "the duplicated population, its declaration sites, and the modules carrying them"
    );

    // Decode each involved module once, keeping only the duplicated rows.
    type Row = (&'static str, Expr, Vec<Name>, Option<Expr>);
    let mut rows: BTreeMap<&String, Vec<Row>> = BTreeMap::new();
    for module in &involved {
        let (infos, _) = decode_at(&lib, module, Level::Private);
        for info in &infos {
            let name = info.name().to_display_string();
            let Some((key, _)) = declarers.get_key_value(&name) else {
                continue;
            };
            let value = match info {
                ConstantInfo::Thm(v) => Some(v.value.clone()),
                ConstantInfo::Defn(v) => Some(v.value.clone()),
                ConstantInfo::Opaque(v) => Some(v.value.clone()),
                _ => None,
            };
            rows.entry(key).or_default().push((
                kind_of(info),
                info.constant_val().type_.clone(),
                info.constant_val().level_params.clone(),
                value,
            ));
        }
    }
    assert_eq!(
        rows.len(),
        declarers.len(),
        "every duplicated name must have been decoded"
    );

    let mut non_theorem: Vec<&&String> = Vec::new();
    let mut disagreeing: Vec<&&String> = Vec::new();
    let mut differing_proofs: Vec<&&String> = Vec::new();
    for (name, found) in &rows {
        assert_eq!(
            found.len(),
            declarers[*name].len(),
            "{name}: one row per declaring module"
        );
        let (kind, type_, levels, value) = &found[0];
        if *kind != "Thm" {
            non_theorem.push(name);
        }
        if found
            .iter()
            .any(|(k, t, l, _)| k != kind || t != type_ || l != levels)
        {
            disagreeing.push(name);
        }
        if found.iter().any(|(_, _, _, v)| v != value) {
            differing_proofs.push(name);
        }
    }

    assert!(
        non_theorem.is_empty(),
        "a multiply-declared DEFINITION would make a differing value a real conflict rather \
         than a benign regeneration; these are not theorems: {non_theorem:?}"
    );
    assert!(
        disagreeing.is_empty(),
        "kind, type and universe parameters must agree in every declaring module: {disagreeing:?}"
    );
    assert_eq!(
        differing_proofs.len(),
        11,
        "the proofs do NOT all agree, and asserting that they do would be false; a decode that \
         lost the difference would report perfect agreement"
    );
    assert!(
        differing_proofs.len() < rows.len(),
        "and the disagreement must be a proper subset, or the type agreement above is being \
         claimed over declarations that share nothing"
    );
}

/// The single reference in `Init.Meta.Defs` that the `import_all` edge is
/// required for.
const IMPORT_ALL_IS_REQUIRED_FOR: &str = "_private.Init.Prelude.0.Lean.Name.beq.match_1";

/// The import closure that respects `import_all`, which the existing closure
/// does not — and it is still total.
///
/// `closure_declared` walks the transitive imports and decodes EVERY member at
/// the requested level. At `Level::Private` that reads every closure member's
/// private part, and a real environment does not get one: an ordinary `import`
/// supplies the exported declarations, and only `import all` supplies the
/// private ones. The helper cannot respect that, because `decode_at` hands back
/// imports as bare `Vec<String>` with the flags discarded before it sees them.
///
/// So the cell above proves `Init.Meta.Defs` is reference-closed at private
/// level against an environment LARGER than Lean would build. The result
/// survives the correction, and the correction is what makes it mean something:
///
///   the permissive closure declares 9,217 names; the flag-respecting one —
///     the module itself at private, its ONE `import_all` target at private,
///     every other member at exported only — declares 8,744, which is 473 fewer
///   all 898 referenced constants still resolve, zero unresolved
///   EXACTLY ONE of them resolves only because of the `import_all` private
///     part, and it is `_private.Init.Prelude.0.Lean.Name.beq.match_1` — the
///     reference this bead observed crossing an import edge in the first place
///
/// That last number is the point. `import_all` is load-bearing here for one
/// name out of 898, so a decode that ignored the flag would look correct on
/// 897 of them; and the earlier "ZERO unresolved" was true while being proved
/// with parts the environment would not have had.
#[test]
fn the_import_closure_that_respects_import_all_is_still_total() {
    let lib = lib_or_skip!();
    const MODULE: &str = "Init.Meta.Defs";

    let (own, _) = decode_at(&lib, MODULE, Level::Private);
    let mut referenced: BTreeSet<String> = BTreeSet::new();
    for info in &own {
        for expr in declaration_expressions(info) {
            referenced.append(&mut referenced_constants(expr));
        }
    }
    let mut available: BTreeSet<String> = own
        .iter()
        .map(|info| info.name().to_display_string())
        .collect();
    assert_eq!(
        (available.len(), referenced.len()),
        (530, 898),
        "{MODULE}: the declaration and reference censuses this row is stated against"
    );

    // The transitive closure at EXPORTED level, which is what an ordinary
    // import supplies.
    let mut visited: BTreeSet<String> = BTreeSet::new();
    let direct = module_view(&lib, MODULE, Level::Private).imports;
    let mut queue: Vec<String> = direct
        .iter()
        .map(|import| import.module.to_display_string())
        .collect();
    while let Some(current) = queue.pop() {
        if !visited.insert(current.clone()) {
            continue;
        }
        let (infos, imports) = decode_at(&lib, &current, Level::Exported);
        available.extend(infos.iter().map(|info| info.name().to_display_string()));
        queue.extend(imports);
    }
    let exported_only = available.clone();

    // And the private parts of exactly the `import all` targets.
    let all_edges: Vec<String> = direct
        .iter()
        .filter(|import| import.import_all)
        .map(|import| import.module.to_display_string())
        .collect();
    assert_eq!(
        all_edges.len(),
        1,
        "{MODULE} carries one import_all edge, which is what makes the difference measurable"
    );
    for module in &all_edges {
        let (infos, _) = decode_at(&lib, module, Level::Private);
        available.extend(infos.iter().map(|info| info.name().to_display_string()));
    }

    let (permissive, missing) = closure_declared(&lib, MODULE, Level::Private);
    assert_eq!(missing, 0, "an absent module would shrink both closures");
    assert!(
        available.len() < permissive.len(),
        "the flag-respecting closure must be strictly smaller, or it is the same computation \
         under another name ({} vs {})",
        available.len(),
        permissive.len()
    );
    assert_eq!(
        (available.len(), permissive.len()),
        (8_744, 9_217),
        "the two closure sizes"
    );

    let unresolved: Vec<&String> = referenced.difference(&available).collect();
    assert!(
        unresolved.is_empty(),
        "{MODULE} stays reference-closed once the closure respects import_all: {unresolved:?}"
    );

    // What the flag actually buys, by name.
    let owed_to_import_all: Vec<&String> = referenced
        .iter()
        .filter(|name| !exported_only.contains(*name))
        .collect();
    assert_eq!(
        owed_to_import_all,
        vec![IMPORT_ALL_IS_REQUIRED_FOR],
        "exactly one reference is resolved only by the import_all private part"
    );
}

/// The one aggregator edge that is not a plain re-export: a meta import.
const AGGREGATOR_META_EDGE: &str = "Init.Try";

/// The library-root module the census leaves out, and the two facts that make
/// leaving it out safe.
///
/// `init_modules` walks `lib/Init` and returns 600 dotted names. The module
/// actually NAMED `Init` is not among them: it lives at `lib/Init.olean`, one
/// level up, outside the directory the walk descends into. Every corpus-width
/// result in this file — 600 modules, 3,153 edges, the acyclicity, the
/// three-way companion bijection — is therefore stated over a set that silently
/// omits it, and nothing said so.
///
/// The omission is safe, for reasons that are measured rather than assumed:
///
///   `Init` declares ZERO constants, so no declaration is missing from any
///     census this file takes
///   NO census module imports `Init`, which is what the import-graph cell's
///     "zero edges leave the set" actually depends on — that cell passes
///     because nobody imports the aggregator, and it never said so
///
/// It is a re-export aggregator with one exception: 43 import edges, every one
/// of them `import_all` false and `is_exported` true — no `import all` anywhere
/// and no declarations of its own — but ONE edge carries `is_meta`, and it is
/// `Init.Try`. The remainder is named rather than folded into "plain
/// re-export", because a predicate widened to accept meta edges would accept
/// them anywhere.
///
/// That exception explains the other oddity instead of sitting beside it: 43
/// edges carry only 42 distinct names, and the repeated one is `Init.Try` —
/// imported once plainly and once as meta. The duplicate row and the meta flag
/// are the same fact, and the cell asserts the link rather than the two counts
/// separately.
///
/// Those 43 edges transitively reach ALL 600 census modules. So the census is
/// exactly what `Init` pulls in, and a module added under `Init/` that the
/// aggregator could not reach would fail here rather than quietly joining a
/// corpus nothing imports.
#[test]
fn the_census_omits_the_aggregator_and_the_aggregator_reaches_the_census() {
    let lib = lib_or_skip!();
    let modules = init_modules(&lib);
    assert_eq!(modules.len(), 600, "the Init module census must be reached");
    assert!(
        !modules.contains(&"Init".to_owned()) && lib.join("Init.olean").is_file(),
        "the module named Init exists and is deliberately outside the census"
    );

    let aggregator = module_view(&lib, "Init", Level::Exported);
    assert_eq!(
        (aggregator.constants, aggregator.imports.len()),
        (0, 43),
        "the aggregator declares nothing and re-exports"
    );
    assert!(
        aggregator
            .imports
            .iter()
            .all(|import| !import.import_all && import.is_exported),
        "no aggregator edge carries import_all, and every one is re-exported"
    );
    let meta: Vec<String> = aggregator
        .imports
        .iter()
        .filter(|import| import.is_meta)
        .map(|import| import.module.to_display_string())
        .collect();
    assert_eq!(
        meta,
        vec![AGGREGATOR_META_EDGE],
        "exactly one aggregator edge is a meta import, and it is named rather than absorbed \
         into `plain re-export`"
    );
    let distinct: BTreeSet<String> = aggregator
        .imports
        .iter()
        .map(|import| import.module.to_display_string())
        .collect();
    assert_eq!(
        distinct.len(),
        42,
        "one edge is repeated, which is this module's instance of a duplicated import row"
    );
    // The repeat and the meta edge are the SAME module: `Init.Try` is imported
    // once plainly and once as meta, which is what makes 43 edges carry 42
    // names.
    assert!(
        aggregator.imports.iter().any(|import| {
            import.module.to_display_string() == AGGREGATOR_META_EDGE && !import.is_meta
        }),
        "the meta edge's module must also appear as a plain edge, or the repeated row and the \
         meta row are unrelated facts"
    );

    // One pass over the census: the adjacency, and whether anything imports the
    // aggregator.
    let census: BTreeSet<&String> = modules.iter().collect();
    let mut edges: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut importing_aggregator: Vec<&String> = Vec::new();
    for module in &modules {
        let targets: Vec<String> = module_view(&lib, module, Level::Exported)
            .imports
            .iter()
            .map(|import| import.module.to_display_string())
            .collect();
        if targets.iter().any(|target| target == "Init") {
            importing_aggregator.push(module);
        }
        edges.insert(module.clone(), targets);
    }
    assert!(
        importing_aggregator.is_empty(),
        "no census module may import the aggregator, or an edge leaves the set the import-graph \
         cell calls closed: {importing_aggregator:?}"
    );

    let mut reached: BTreeSet<String> = BTreeSet::new();
    let mut queue: Vec<String> = distinct.iter().cloned().collect();
    while let Some(current) = queue.pop() {
        if !census.contains(&current) || !reached.insert(current.clone()) {
            continue;
        }
        queue.extend(edges[&current].iter().cloned());
    }
    assert_eq!(
        reached.len(),
        modules.len(),
        "the aggregator must reach every census module; unreachable: {:?}",
        census
            .iter()
            .filter(|module| !reached.contains(**module))
            .take(8)
            .collect::<Vec<_>>()
    );
}
