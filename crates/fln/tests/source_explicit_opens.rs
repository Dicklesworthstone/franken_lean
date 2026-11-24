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

#[test]
fn hiding_excludes_only_the_exact_name_in_that_open() {
    for source in [
        format!("{FOO}open Foo hiding x\ntheorem t : y = 2 := rfl\ntheorem u : Foo.x = 1 := rfl\n"),
        format!("{FOO}open Foo\nopen Foo hiding x\ntheorem t : x = 1 := rfl\n"),
        format!("{FOO}open Foo hiding x\nopen Foo\ntheorem t : x = 1 := rfl\n"),
        format!("{FOO}open Foo hiding x\nopen Foo hiding y\ntheorem t : x + y = 3 := rfl\n"),
        format!("{FOO}def Foo.x.next : Nat := 3\nopen Foo hiding x\ntheorem t : x.next = 3 := rfl\n"),
        format!("{FOO}namespace N\nexport Foo (x y)\nend N\nopen N hiding x\ntheorem t : y = 2 := rfl\n"),
        "open Nat hiding add\ntheorem t : succ 1 = 2 := rfl\n".to_owned(),
        "namespace Foo\ndef «a.b» : Nat := 1\ndef a.b : Nat := 2\nend Foo\nopen Foo hiding «a.b»\ntheorem t : a.b = 2 := rfl\n".to_owned(),
        "def Foo.Child : Nat := 1\ndef Foo.Child.x : Nat := 2\nopen Foo hiding Child\ntheorem t : Child.x = 2 := rfl\n".to_owned(),
    ] {
        check(&source).unwrap_or_else(|error| panic!("{source}: {error}"));
    }
}

#[test]
fn hiding_validates_the_namespace_and_members_and_stays_lexical() {
    for source in [
        format!("{FOO}open Foo hiding x\n#check x\n"),
        format!("{FOO}open Foo hiding absent\n"),
        format!("{FOO}open Foo hiding x in\ntheorem t : y = 2 := rfl\n#check y\n"),
        format!("{FOO}section\nopen Foo hiding x\nend\n#check y\n"),
        "namespace A.N\ndef x : Nat := 1\nend A.N\nnamespace B.N\ndef x : Nat := 2\nend B.N\nopen A B\nopen N hiding x\n".to_owned(),
        "namespace A.N\ndef x : Nat := 1\nend A.N\nopen A\nopen A\nopen N hiding x\n".to_owned(),
        "def Foo.Child : Nat := 1\ndef Foo.Child.x : Nat := 2\nopen Foo hiding Child\nopen Child\n".to_owned(),
    ] {
        assert!(check(&source).is_err(), "{source}");
    }
}

#[test]
fn hiding_still_activates_scoped_instances() {
    check(
        "class Pick where\n  value : Nat\n\
         def fallback : Pick := Pick.mk 1\n\
         attribute [instance] fallback\n\
         def chosen [p : Pick] : Nat := Pick.value\n\
         namespace Chosen\n\
         def hidden : Nat := 7\n\
         def override : Pick := Pick.mk 2\n\
         attribute [scoped instance] override\n\
         end Chosen\n\
         open Chosen hiding hidden\n\
         theorem selected : chosen = 2 := rfl\n",
    )
    .unwrap();
}
