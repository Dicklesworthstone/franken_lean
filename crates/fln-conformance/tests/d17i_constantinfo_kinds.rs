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
