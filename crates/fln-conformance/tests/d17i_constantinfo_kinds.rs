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

use fln_core::expr::{Expr, ExprNode};
use fln_core::name::Name;
use fln_env::constants::ConstantInfo;
use fln_olean::decl::DeclDecoder;
use fln_olean::region::{OleanView, WalkBudget};

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
