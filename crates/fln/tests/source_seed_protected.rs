//! A headerless file runs on the source seed, which carries the pin's `protected`
//! marks for its own constants (bead `fln-8xz8`): `open Nat` does not make the
//! protected `Nat.add` available as `add`, exactly as under the pin's implicit
//! `import Init`.
//!
//! The marks come from `fln_elab::seed::protected`'s table, generated from the pinned
//! `lean` by `scripts/extract/gen_seed_protected.sh` (which also regenerates it to a
//! scratch file and diffs it, `--check`). Every program's expected verdict is the
//! pinned Reference's own, each run alone as a headerless file:
//!
//! ```text
//! ulimit -v 40000000
//! ~/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean file.lean
//! ```
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};
use fln_elab::aliases::AliasTable;
use fln_elab::protected_names::ProtectedNames;
use fln_elab::seed::protected::{PinStatus, seed_pin_statuses, seed_protected_names};
use fln_elab::source::scope::{ScopeError, SourceScope};
use std::collections::BTreeSet;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn seed() -> Engine {
    Engine::with_source_seed(limits())
        .expect("the source seed builds")
        .into_complete()
        .expect("the source seed completes")
}

/// Refused by the pin, each run headerless on 2026-10-06. First errors:
/// `2:15: error(lean.unknownIdentifier): Unknown identifier `add`` for the first two,
/// and `2:12: error: Function expected at add` for the third, whose `add` sits in a
/// theorem's signature, where the pin's `autoImplicit` binds an unknown identifier as
/// a variable before applying it (its hint: "The identifier `add` is unknown"; with
/// `set_option autoImplicit false` the pin reports `Unknown identifier `add`` there
/// too). FrankenLean binds no auto-implicits, so all three are refused as the unknown
/// identifier the pin finds.
const REFUSED: &[(&str, &str)] = &[
    (
        "open Nat\ndef u : Nat := add 1 2",
        "Unknown identifier `add`",
    ),
    (
        "open Nat in\ndef u : Nat := add 1 2",
        "Unknown identifier `add`",
    ),
    (
        "open Nat\ntheorem t : add 1 2 = 3 := by decide",
        "Unknown identifier `add`",
    ),
];

/// Accepted by the pin (exit 0), run as above: the unprotected constructor by its
/// atomic name, and the protected `Nat.add` by its full one.
const ACCEPTED: &[&str] = &[
    "open Nat\ndef u : Nat := succ 1",
    "open Nat\ndef u : Nat := Nat.add 1 2",
    "open Nat in\ndef u : Nat := Nat.add 1 2",
];

/// Seed constants the pin does not have (`absent` in the generated table), named from
/// source. Each was accepted here until fln-ew20: the seed defined it, so a program
/// naming it was a false accept. Refused by the pin, each run headerless on
/// 2026-10-06, with the first error quoted. Three were seed instances under names of
/// FrankenLean's own; they now carry the pin's (below), and the fourth, an internal
/// dictionary with no pin counterpart, is refused by name
/// (`fln_elab::seed::protected::source_unreachable`). The class is FrankenLean's own:
/// an `attribute` naming nothing is an `input` refusal, a term naming nothing an
/// `elaboration` one.
const REFUSED_ABSENT: &[(&str, &str, &str)] = &[
    (
        "attribute [instance] instDecidableEqOption",
        "Unknown constant `instDecidableEqOption`",
        "input",
    ),
    (
        "attribute [instance] instInhabitedString",
        "Unknown constant `instInhabitedString`",
        "input",
    ),
    (
        "attribute [instance] instDecidableImplies",
        "Unknown constant `instDecidableImplies`",
        "input",
    ),
    (
        "def b : BEq String := _fln_numeric.beqString",
        "Unknown identifier `_fln_numeric.beqString`",
        "elaboration",
    ),
    (
        "attribute [instance] _fln_numeric.beqString",
        "Unknown constant `_fln_numeric.beqString`",
        "input",
    ),
];

/// Accepted by the pin (exit 0), run as above: the pin's own names for the three
/// renamed seed instances, and `decide` and `default`, which the pin has only as
/// `export` aliases (status `alias` in the table, so never refused by name).
const ACCEPTED_PIN_NAMES: &[&str] = &[
    "attribute [instance] Option.instDecidableEq",
    "attribute [instance] String.instInhabited",
    "attribute [instance] instDecidableForall",
    "def d : Bool := decide (1 = 1)",
    "def e : Nat := default",
];

#[test]
fn seed_names_the_pin_does_not_have_are_refused_as_the_pin_refuses_them() {
    let engine = seed();
    for (source, wording, expected_class) in REFUSED_ABSENT {
        let error = engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .expect_err(source);
        let text = error.to_string();
        assert!(
            text.contains(wording),
            "{source} must be refused with `{wording}`, as the pin refuses it: {text}"
        );
        let (class, authority, _) = error.disposition();
        assert_eq!(
            (class, authority),
            (*expected_class, false),
            "{source}: {error}"
        );
    }
    for source in ACCEPTED_PIN_NAMES {
        let checked = engine.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        );
        assert!(
            matches!(checked, Ok(Outcome::Complete(_))),
            "{source} must be admitted, as the pin admits it: {checked:?}"
        );
    }
}

/// Every seed constant the table marks `absent` is refused by name, and nothing else
/// is: the refusal is derived from the table, never listed. `decide` and `default`
/// are `alias` rows, reachable at the pin through `export`, so they stay reachable.
#[test]
fn exactly_the_tables_absent_rows_are_source_unreachable() {
    let rows = seed_pin_statuses().expect("the generated table reads");
    let mut absent = 0;
    for (name, status) in &rows {
        assert_eq!(
            fln_elab::seed::protected::source_unreachable(name),
            *status == PinStatus::Absent,
            "{}: {status:?}",
            name.to_display_string()
        );
        absent += usize::from(*status == PinStatus::Absent);
    }
    assert!(
        absent > 0,
        "the table has an absent row; a scan finding none is broken"
    );
    for alias in ["decide", "default"] {
        assert!(
            rows.iter()
                .any(|(name, status)| *name == Name::from_components([alias])
                    && *status == PinStatus::Alias),
            "the pin reaches `{alias}` only as an export alias"
        );
    }
}

#[test]
fn the_pins_refusals_of_protected_seed_names_are_refused_at_elaboration() {
    let engine = seed();
    for (source, wording) in REFUSED {
        let error = engine
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .expect_err(source);
        let text = error.to_string();
        assert!(
            text.contains("elaboration refused source") && text.contains(wording),
            "{source} must be refused at elaboration with `{wording}`, as the pin refuses it: {text}"
        );
        let (class, authority, _) = error.disposition();
        assert_eq!(
            (class, authority),
            ("elaboration", false),
            "{source}: {error}"
        );
    }
    for source in ACCEPTED {
        let checked = engine.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        );
        assert!(
            matches!(checked, Ok(Outcome::Complete(_))),
            "{source} must be admitted, as the pin admits it: {checked:?}"
        );
    }
}

/// The table names exactly the seed's constants, and the seed's journal marks exactly
/// the ones the pin protects: nothing protected is missed, nothing else is held back.
#[test]
fn the_seed_carries_exactly_the_pins_protected_marks() {
    let engine = seed();
    let env = engine.environment();
    let rows = seed_pin_statuses().expect("the generated table reads");
    let listed: BTreeSet<Name> = rows.iter().map(|(name, _)| name.clone()).collect();
    let constants: BTreeSet<Name> = env.constants().map(|(name, _)| name.clone()).collect();
    assert_eq!(
        listed.difference(&constants).collect::<Vec<_>>(),
        Vec::<&Name>::new(),
        "the table lists constants the seed lacks: regenerate it"
    );
    assert_eq!(
        constants.difference(&listed).collect::<Vec<_>>(),
        Vec::<&Name>::new(),
        "seed constants the table does not list: regenerate it"
    );
    let expected: BTreeSet<Name> = seed_protected_names()
        .expect("the generated table reads")
        .into_iter()
        .collect();
    let marked: BTreeSet<Name> = ProtectedNames::read(env)
        .expect("the seed's protected journal reads")
        .iter()
        .cloned()
        .collect();
    assert_eq!(marked, expected);
    assert!(
        expected.contains(&Name::from_components(["Nat", "add"])),
        "the pin marks Nat.add protected"
    );
    assert!(
        rows.iter().any(
            |(name, status)| *name == Name::from_components(["Nat", "succ"])
                && *status == PinStatus::Unprotected
        ),
        "the pin leaves Nat.succ unprotected"
    );
}

/// Every seed constant the pin marks protected: never the resolution of its atomic
/// name under `open` of its namespace or inside that namespace, and still reached by
/// its full name. The control runs the same lookups with no marks, where the atomic
/// name does reach the declaration: alone, or beside a root constant of that atomic
/// name (the seed's root `decEq` beside the protected `Nat.decEq` under `open Nat`),
/// which the pin pools with it as a candidate (bead `fln-wh2j`).
#[test]
fn every_protected_seed_declaration_is_held_back_from_its_atomic_name() {
    let engine = seed();
    let env = engine.environment();
    let aliases = AliasTable::read(env).expect("the alias journal reads");
    let protected = ProtectedNames::read(env).expect("the protected journal reads");
    let unmarked = ProtectedNames::default();
    let exists = |candidate: &Name| env.contains(candidate);
    let names = seed_protected_names().expect("the generated table reads");
    assert!(!names.is_empty());
    for name in &names {
        let spelled = name.to_display_string();
        assert!(
            spelled.contains('.'),
            "{spelled}: the pin protects only namespaced names"
        );
        let (prefix, last) = spelled
            .rsplit_once('.')
            .expect("a namespaced name has a last component");
        let namespace = Name::from_components(prefix.split('.'));
        let atomic = Name::from_components([last]);
        let opened = SourceScope {
            opened: vec![namespace.clone()],
            ..SourceScope::default()
        };
        let inside = SourceScope {
            namespace: namespace.clone(),
            ..SourceScope::default()
        };
        for (how, scope) in [("open", &opened), ("namespace", &inside)] {
            let resolved = scope.resolve_with_aliases(&atomic, exists, &aliases, &protected);
            assert!(
                !matches!(&resolved, Ok(Some(found)) if found == name)
                    && !matches!(&resolved, Err(ScopeError::Ambiguous(_, candidates)) if candidates.contains(name)),
                "{how} {prefix}: `{last}` must not reach the protected {spelled}: {resolved:?}"
            );
            let control = scope.resolve_with_aliases(&atomic, exists, &aliases, &unmarked);
            assert!(
                matches!(&control, Ok(Some(found)) if found == name)
                    || matches!(&control, Err(ScopeError::Ambiguous(_, candidates)) if candidates.contains(name)),
                "{how} {prefix}: unmarked, `{last}` reaches {spelled}: {control:?}"
            );
            assert_eq!(
                scope.resolve_with_aliases(name, exists, &aliases, &protected),
                Ok(Some(name.clone())),
                "{how} {prefix}: {spelled} stays reachable by its full name"
            );
        }
    }
}
