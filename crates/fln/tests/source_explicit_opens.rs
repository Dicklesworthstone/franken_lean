//! `open Ns (a b …)` (`openOnly`), as the pin's `elabOpenDecl`:
//! - `Ns` resolves as `open` resolves it;
//! - each name must denote one declaration `ns ++ name`;
//! - `OpenDecl.explicit a Ns.a` then answers `a` (and `a.b` when `Ns.a.b` exists) without the
//!   protection test, until the end of the section.
//!
//! The explicit-open and renaming programs were checked against pinned Lean v4.32.0
//! over `prelude` + `import Init.Core`.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(source: &str) -> Result<(), String> {
    match engine().check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    ) {
        Ok(outcome) => {
            outcome.into_complete().unwrap();
            Ok(())
        }
        Err(error) => Err(error.to_string()),
    }
}

const FOO: &str = "namespace Foo\ndef x : Nat := 1\ndef y : Nat := 2\nend Foo\n";

#[test]
fn explicitly_opened_names_resolve_to_their_declarations() {
    for source in [
        format!("{FOO}open Foo (x)\ntheorem t : x = 1 := rfl\n"),
        format!("{FOO}open Foo (x y)\ntheorem t : x + y = 3 := rfl\n"),
        "open Nat (succ)\ntheorem t : succ 1 = 2 := rfl\n".to_string(),
        // `Nat.add` is protected; an explicit open reaches it anyway.
        "open Nat (add)\ntheorem t : add 1 2 = 3 := rfl\n".to_string(),
        format!("{FOO}section\nopen Foo (x)\ntheorem t : x = 1 := rfl\nend\n"),
    ] {
        check(&source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
}

#[test]
fn explicit_open_refusals_match_the_pin() {
    for (source, pin) in [
        (format!("{FOO}open Foo (z)\n"), "Unknown identifier"),
        // Only the listed names are opened.
        (
            format!("{FOO}open Foo (x)\ntheorem t : y = 2 := rfl\n"),
            "Not a definitional equality (`y` is auto-bound)",
        ),
        // The open ends with its section.
        (
            format!("{FOO}section\nopen Foo (x)\nend\ntheorem t : x = 1 := rfl\n"),
            "Not a definitional equality (`x` is auto-bound)",
        ),
        (
            format!("{FOO}open Foo (x)\ntheorem t : x = 2 := rfl\n"),
            "Not a definitional equality",
        ),
        ("open Nope (x)\n".to_string(), "unknown namespace `Nope`"),
    ] {
        assert!(
            check(&source).is_err(),
            "accepted {source} (the pin: {pin})"
        );
    }
}

#[test]
fn renamed_opens_resolve_protected_exported_and_preceding_names() {
    for source in [
        format!(
            "{FOO}open Foo renaming x → leftValue, y -> rightValue\ntheorem t : leftValue + rightValue = 3 := rfl\n"
        ),
        format!("{FOO}open Foo renaming x → Foo.w, w → twice\ntheorem t : twice = 1 := rfl\n"),
        format!(
            "{FOO}namespace N\nexport Foo (x)\nend N\nopen N renaming x → chosen\ntheorem t : chosen = 1 := rfl\n"
        ),
        format!(
            "{FOO}def Foo.x.next : Nat := 3\nopen Foo renaming x → a\ntheorem t : a.next = 3 := rfl\n"
        ),
        format!("{FOO}open Foo renaming x → aliasValue in\ntheorem t : aliasValue = 1 := rfl\n"),
        "open Nat renaming add → total\ntheorem t : total 1 2 = 3 := rfl\n".to_owned(),
    ] {
        check(&source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
}

#[test]
fn renamed_opens_require_a_unique_namespace_and_stay_lexical() {
    for source in [
        format!("{FOO}section\nopen Foo renaming x → aliasValue\nend\n#check aliasValue\n"),
        format!("{FOO}open Foo renaming x → aliasValue in\ntheorem t : aliasValue = 1 := rfl\n#check aliasValue\n"),
        format!("{FOO}open Foo renaming x → aliasValue\n#check x\n"),
        format!("{FOO}open Foo renaming x → aliasValue, z → missingValue\n"),
        format!("{FOO}open Foo renaming x →\ny\n"),
        "namespace A.N\ndef x : Nat := 1\nend A.N\nnamespace B.N\ndef y : Nat := 2\nend B.N\nopen A B\nopen N renaming x → chosen\n".to_owned(),
    ] {
        assert!(check(&source).is_err(), "{source}");
    }
}
