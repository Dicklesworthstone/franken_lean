//! Names that resolve to more than one declaration (bead `fln-wh2j`), headerless, as
//! `fln check-source` runs them: on the source seed and on the coercion seed it builds
//! for a file without a header.
//!
//! The pin's `resolveGlobalName` (vendored `src/Lean/ResolveName.lean:194-217`) pools a
//! root declaration with each opened namespace's: under `open P`, `foo` names both
//! `_root_.foo` and `P.foo`, and its `elabAppAux` (vendored `src/Lean/Elab/App.lean`)
//! refuses the identifier as "Ambiguous term" unless the expected type leaves exactly
//! one interpretation. Before this bead FrankenLean took the root declaration.
//!
//! Every program's expected verdict is the pinned Reference's own, each run alone as
//! a headerless file on 2026-10-06:
//!
//! ```text
//! ulimit -v 40000000
//! ~/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean file.lean
//! ```
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

/// The engines a headerless file is checked on: the source seed, and the coercion seed
/// `fln check-source` builds on it.
fn seeds() -> [(&'static str, Engine); 2] {
    [
        (
            "source seed",
            Engine::with_source_seed(limits())
                .expect("the source seed builds")
                .into_complete()
                .expect("the source seed completes"),
        ),
        (
            "coercion seed",
            Engine::with_coercion_seed(limits())
                .expect("the coercion seed builds")
                .into_complete()
                .expect("the coercion seed completes"),
        ),
    ]
}

const BOTH: &str = "def foo : Nat := 1\nnamespace P\ndef foo : Nat := 2\nend P\n";

/// Refused by the pin with "Ambiguous term foo", each listing its interpretations
/// root first, then the opened namespaces most recently opened first:
/// `_root_.foo : Nat`, `P.foo : Nat` (with `Q.foo : Nat` between them for the
/// third program, and `_root_.foo 1 : Nat`, `P.foo 1 : Nat` for the application).
const AMBIGUOUS: &[(&str, &str)] = &[
    (
        "open P\ndef bar : Nat := foo",
        "Ambiguous term `foo`; Possible interpretations: `_root_.foo`, `P.foo`",
    ),
    (
        "open P in\ndef bar : Nat := foo",
        "Ambiguous term `foo`; Possible interpretations: `_root_.foo`, `P.foo`",
    ),
    (
        "open P\ntheorem t : foo = 1 := rfl",
        "Ambiguous term `foo`; Possible interpretations: `_root_.foo`, `P.foo`",
    ),
    (
        "namespace Q\ndef foo : Nat := 3\nend Q\nopen P\nopen Q\ndef bar : Nat := foo",
        "Ambiguous term `foo`; Possible interpretations: `_root_.foo`, `Q.foo`, `P.foo`",
    ),
];

/// The application form, with its own declarations: refused by the pin as above.
const AMBIGUOUS_APPLICATION: &str = "def foo (n : Nat) : Nat := n\nnamespace P\ndef foo (n : Nat) : Nat := n + 1\nend P\nopen P\ndef bar : Nat := foo 1";

/// Accepted by the pin (exit 0): a name written so it names one declaration, an inner
/// namespace's declaration (found before the root and the opened ones), a name only an
/// opened namespace provides, a local, and the declaration's own recursive reference.
const ACCEPTED: &[&str] = &[
    "open P\ndef bar : Nat := P.foo",
    "open P\ndef bar : Nat := _root_.foo",
    "namespace A\ndef foo : Nat := 3\nopen P\ndef bar : Nat := foo\nend A",
    "open P\ndef bar (foo : Nat) : Nat := foo",
    "namespace R\ndef only : Nat := 2\nend R\nopen R\ndef bar : Nat := only",
    "namespace S\ndef walk : Nat := 2\nend S\nopen S\ndef walk (n : Nat) : Nat := match n with | .zero => 0 | .succ k => walk k",
];

/// Refused by the pin ("fail to show termination for A.foo"): in `namespace A`,
/// `def foo : Nat := foo` names the declaration being defined, never the root `foo`,
/// which FrankenLean took before this bead.
const OWN_NAME_REFUSED: &[&str] = &[
    "namespace A\ndef foo : Nat := foo\nend A",
    "namespace A\ndef foo : Nat := foo + 1\nend A",
];

/// Accepted by the pin, which rules out `P.foo` because its type is not `Nat` and its
/// `Init` has no coercion to `Nat`. A seed stages coercion classes but not the pin's
/// `Init` coercions, so it cannot establish that, and FrankenLean refuses these rather
/// than choose: a non-authoritative refusal. Against the pin's own `Init.Core` it
/// chooses as the pin does (`source_import_aliases.rs`).
const UNDETERMINED_HERE: &[&str] = &[
    "def foo : Nat := 1\nnamespace P\ndef foo : Bool := true\nend P\nopen P\ndef bar : Nat := foo",
    "def foo (n : Nat) : Nat := n\nnamespace P\ndef foo (_n : Nat) : Bool := true\nend P\nopen P\ndef bar : Nat := foo 1",
];

fn check(
    engine: &Engine,
    source: &str,
) -> Result<Outcome<fln::SourceFileCheck>, fln::SourceCheckError> {
    engine.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
}

#[test]
fn a_root_declaration_and_an_opened_one_are_ambiguous_as_at_the_pin() {
    for (seed, engine) in seeds() {
        let root = engine.logical_root(&KVMap::new());
        let mut programs: Vec<(String, &str)> = AMBIGUOUS
            .iter()
            .map(|(body, wording)| (format!("{BOTH}{body}"), *wording))
            .collect();
        programs.push((
            AMBIGUOUS_APPLICATION.to_owned(),
            "Ambiguous term `foo`; Possible interpretations: `_root_.foo`, `P.foo`",
        ));
        for (source, wording) in programs {
            let error = check(&engine, &source).expect_err(&source);
            let text = error.to_string();
            assert!(
                text.contains("elaboration refused source") && text.contains(wording),
                "{seed}: {source} must be refused with `{wording}`, as the pin refuses it: {text}"
            );
            assert_eq!(
                error.disposition().0,
                "elaboration",
                "{seed}: {source}: {error}"
            );
        }
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn names_that_name_one_declaration_are_accepted_as_at_the_pin() {
    for (seed, engine) in seeds() {
        for body in ACCEPTED {
            let source = format!("{BOTH}{body}");
            let checked = check(&engine, &source);
            assert!(
                matches!(checked, Ok(Outcome::Complete(_))),
                "{seed}: {source} must be admitted, as the pin admits it: {checked:?}"
            );
        }
        for source in OWN_NAME_REFUSED {
            let source = format!("{BOTH}{source}");
            assert!(
                check(&engine, &source).is_err(),
                "{seed}: {source} must be refused, as the pin refuses it"
            );
        }
    }
}

#[test]
fn a_seed_refuses_rather_than_choose_by_type() {
    for (seed, engine) in seeds() {
        for source in UNDETERMINED_HERE {
            let error = check(&engine, source).expect_err(source);
            let (class, authority, _) = error.disposition();
            assert_eq!(
                (class, authority),
                ("elaboration", false),
                "{seed}: {error}"
            );
            assert!(
                error.to_string().contains(
                    "the interpretation `P.foo` can be neither established nor ruled out"
                ),
                "{seed}: {source}: {error}"
            );
        }
    }
}
