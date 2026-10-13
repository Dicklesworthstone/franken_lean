//! A `protected` declaration made by an executed command, in the seed world: as the pin's
//! `addProtected` leaves it, a later command's atomic name does not reach it through its
//! namespace, an `open` or an `export` alias (`resolveQualifiedName` and `getAliases …
//! (skipProtected := id.isAtomic)`, vendored `Lean/ResolveName.lean`). The execution path tags it
//! as the check path does. A definition it compiles and a theorem or template it only admits are
//! both tagged, and a protected definition still runs under its full name. These are the shapes
//! of `fln-cli`'s `source_protected_aliases`, which runs each program through the pinned `lean`
//! v4.32.0 first.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, VmExit};

fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    Engine::with_source_seed(EngineAdmissionLimits::new(limits().kernel))
        .unwrap()
        .into_complete()
        .unwrap()
}

fn execute(source: &str) -> Result<Option<String>, String> {
    match engine().execute_source_definitions(&[source.as_bytes()], &KVMap::new(), limits()) {
        Ok(outcome) => {
            let run = outcome.into_complete().unwrap();
            Ok(match &run.executions.last().unwrap().exit {
                VmExit::Returned(value) => fln_vm::interpreter::nat_decimal(&value.value),
                _ => None,
            })
        }
        Err(error) => Err(format!("{error:?}")),
    }
}

const DOUBLE: &str = "protected def Foo.double (x : Nat) : Nat := x + x\n";

#[test]
fn an_atomic_name_does_not_reach_a_protected_declaration() {
    for program in [
        "open Foo\ndef y : Nat := double 3\n",
        "namespace Foo\ndef y : Nat := double 3\nend Foo\n",
        "namespace Ex\nexport Foo (double)\nend Ex\nopen Ex\ndef y : Nat := double 3\n",
        "export Foo (double)\ndef y : Nat := double 3\n",
    ] {
        let source = format!("{DOUBLE}{program}");
        assert!(execute(&source).is_err(), "accepted {source}");
    }
    // A protected theorem is admitted, not compiled; it is tagged the same way.
    let theorem = "protected theorem Foo.self (n : Nat) : n = n := rfl\nopen Foo\n\
                   theorem t : 3 = 3 := self 3\n";
    assert!(execute(theorem).is_err(), "accepted {theorem}");
}

#[test]
fn a_protected_definition_runs_under_its_full_name() {
    for (program, value) in [
        ("open Foo\ndef y : Nat := Foo.double 3\n#eval y\n", "6"),
        (
            "namespace Ex\nexport Foo (double)\nend Ex\ndef y : Nat := Ex.double 4\n#eval y\n",
            "8",
        ),
    ] {
        let source = format!("{DOUBLE}{program}");
        assert_eq!(
            execute(&source).unwrap_or_else(|error| panic!("{source}: {error}")),
            Some(value.to_owned()),
            "{source}"
        );
    }
}
