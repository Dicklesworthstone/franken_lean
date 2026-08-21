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

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

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
