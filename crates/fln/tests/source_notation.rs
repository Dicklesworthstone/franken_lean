//! A file's own notation, end to end: declared, parsed in the commands after it, expanded with
//! the pin's hygiene, elaborated and kernel-checked (bead `franken_lean-z8j.1.10`, stage 4).
//!
//! Every program's verdict was taken from the pinned `lean` (v4.32.0) on 2026-10-09 first.
#![forbid(unsafe_code)]
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionError, EngineExecutionLimits, KVMap,
    SourceCheckError, SourceCheckLimits, VmExit,
};

fn check(source: &str) -> Result<usize, SourceCheckError> {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .map(|outcome| outcome.into_complete().unwrap().theorems)
}

fn accepted(source: &str) {
    let theorems = check(source).unwrap_or_else(|error| panic!("{source}\n{error:?}"));
    assert_eq!(theorems, 1, "{source}");
}

fn refused(source: &str) -> SourceCheckError {
    match check(source) {
        Ok(_) => panic!("the pin refuses this program:\n{source}"),
        Err(error) => error,
    }
}

const ADD: &str = "def myAdd (a b : Nat) : Nat := Nat.add a b\n";

/// `infixl`, `prefix` and a bracketed `notation`: accepted at the pin (exit 0).
#[test]
fn declared_notation_elaborates_through_its_expansion() {
    accepted(&format!(
        "{ADD}infixl:65 \" +++ \" => myAdd\ntheorem t : (2 : Nat) +++ 3 = 5 := rfl\n"
    ));
    accepted(
        "def neg2 (a : Nat) : Nat := Nat.add a a\nprefix:max \"√\" => neg2\n\
         theorem p : √(2 : Nat) = 4 := rfl\n",
    );
    accepted("notation \"⟪\" x \"⟫\" => Nat.add x x\ntheorem d : ⟪(3 : Nat)⟫ = 6 := rfl\n");
}

/// An operator with both spellings (`unicode(" ⊕⊕ ", " +|+ ")`, as Init/Notation.lean declares `≤`
/// and `∧`): either spelling is the notation (the pin accepts both), and the expansion is still
/// checked (the pin: "Not a definitional equality").
#[test]
fn a_unicode_operator_elaborates_under_both_spellings() {
    let declared = format!("{ADD}infixl:65 unicode(\" ⊕⊕ \", \" +|+ \") => myAdd\n");
    accepted(&format!(
        "{declared}theorem t : (2 : Nat) ⊕⊕ 3 = 5 := rfl\n"
    ));
    accepted(&format!(
        "{declared}theorem t : (2 : Nat) +|+ 3 = 5 := rfl\n"
    ));
    refused(&format!(
        "{declared}theorem t : (2 : Nat) +|+ 3 = 6 := rfl\n"
    ));
}

/// A template's name means what it meant where the notation was declared: the theorem's binder
/// `myAdd` does not capture it (the pin accepts, with an unused-variable warning).
#[test]
fn a_template_name_is_not_captured_by_a_binder_at_the_use() {
    accepted(&format!(
        "{ADD}infixl:65 \" +++ \" => myAdd\n\
         theorem t (myAdd : Nat → Nat → Nat) : (2 : Nat) +++ 3 = 5 := rfl\n"
    ));
}

/// The expansion is checked like any term: a false equation is refused (the pin: "Not a
/// definitional equality").
#[test]
fn an_expanded_false_equation_is_refused() {
    refused(&format!(
        "{ADD}infixl:65 \" +++ \" => myAdd\ntheorem t : (2 : Nat) +++ 3 = 6 := rfl\n"
    ));
}

/// The quotation precheck: the pin refuses `infixl … => nope` at the declaration ("Unknown
/// identifier `nope` at quotation precheck"), used or not.
#[test]
fn an_unknown_template_name_is_refused_at_the_declaration() {
    let error = refused("infixl:65 \" +++ \" => nope\ntheorem x : (1 : Nat) = 1 := rfl\n");
    assert!(
        matches!(&error, SourceCheckError::Command { command: 0, .. }),
        "{error:?}"
    );
}

/// `scoped` notation is active inside its namespace and gone after its `end` (the pin refuses
/// the use outside: "unexpected token '+'").
#[test]
fn scoped_notation_lives_in_its_namespace() {
    accepted(
        "namespace Foo\nscoped infixl:65 \" +++ \" => Nat.add\n\
         theorem s : (2 : Nat) +++ 3 = 5 := rfl\nend Foo\n",
    );
    refused(
        "namespace Foo\nscoped infixl:65 \" +++ \" => Nat.add\nend Foo\n\
         theorem s : (2 : Nat) +++ 3 = 5 := rfl\n",
    );
}

/// A template that binds names (`fun y => …`) is accepted at the pin; its scoping is not
/// prechecked here, so it is refused as not implemented rather than admitted unchecked.
#[test]
fn a_template_that_binds_names_is_a_typed_refusal() {
    let error = refused(
        "notation \"⟪\" x \"⟫\" => (fun y => Nat.add y y) x\ntheorem w : ⟪(2 : Nat)⟫ = 4 := rfl\n",
    );
    assert!(
        matches!(&error, SourceCheckError::Command { error, .. }
            if matches!(**error, EngineExecutionError::NotImplemented { .. })),
        "{error:?}"
    );
}

/// A token the file declares is one in the commands after it, on the execute path (`lean`'s) too:
/// the pin prints 42.
#[test]
fn a_declared_token_lexes_in_the_commands_after_it_when_executing() {
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    let completed = engine
        .execute_source_commands_with_checks(
            "def double (n : Nat) : Nat := 2 * n\nnotation \"⟪\" n \"⟫\" => double n\n#eval ⟪21⟫\n"
                .as_bytes(),
            &KVMap::new(),
            limits,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let VmExit::Returned(returned) = &completed.batch.executions.last().unwrap().exit else {
        panic!("VM return")
    };
    assert_eq!(
        fln_vm::interpreter::nat_decimal(&returned.value).as_deref(),
        Some("42")
    );
}

/// Before its declaration the token is none: the pin refuses the use ("expected token") at the
/// first command.
#[test]
fn a_use_before_the_declaration_is_refused() {
    let error =
        refused("theorem early : ⟪(2 : Nat)⟫ = 4 := rfl\nnotation \"⟪\" n \"⟫\" => Nat.add n n\n");
    assert!(
        matches!(&error, SourceCheckError::Command { command: 0, .. }),
        "{error:?}"
    );
}

/// Only the file's own syntax is entered here: Init's `{}` notation is not, so `{}` is still the
/// structure instance beside a declared notation (the pin accepts, resolving its `choice`).
#[test]
fn a_structure_instance_reads_as_before_beside_a_declared_notation() {
    let source = "structure C where\n  x : Nat := 3\nnotation \"⟪\" n \"⟫\" => Nat.add n n\n\
                  def c : C := {}\ntheorem t : c.x = 3 := rfl\ntheorem u : ⟪(2 : Nat)⟫ = 4 := rfl\n";
    let theorems = check(source).unwrap_or_else(|error| panic!("{source}\n{error:?}"));
    assert_eq!(theorems, 2, "{source}");
}

/// A template's names mean what they meant where the notation was declared (the quotation's
/// pre-resolution): `X` is `A.foo` after `end A`, a root `foo` notwithstanding. The pin refuses
/// `X = 2` ("Not a definitional equality") and accepts `X = 1`.
#[test]
fn a_template_name_keeps_the_declaration_it_named_where_declared() {
    let prefix =
        "namespace A\ndef foo : Nat := 1\nnotation \"X\" => foo\nend A\ndef foo : Nat := 2\n";
    refused(&format!("{prefix}theorem t : X = 2 := rfl\n"));
    accepted(&format!("{prefix}theorem t : X = 1 := rfl\n"));
}

/// A `macro`, a tactic `macro`, and `syntax` with its `macro_rules` expand where they are used,
/// as at the pin (which accepts all three theorems).
#[test]
fn macros_expand_where_they_are_used() {
    let source = "def myAdd (a b : Nat) : Nat := Nat.add a b\n\
                  macro \"dbl \" x:term:max : term => `(myAdd $x $x)\n\
                  theorem t : dbl (3 : Nat) = 6 := rfl\n\
                  macro \"my_rfl\" : tactic => `(tactic| rfl)\n\
                  theorem u : (2 : Nat) = 2 := by my_rfl\n\
                  syntax \"trip \" term:max : term\n\
                  macro_rules | `(trip $x) => `(myAdd $x (myAdd $x $x))\n\
                  theorem v : trip (2 : Nat) = 6 := rfl\n";
    let theorems = check(source).unwrap_or_else(|error| panic!("{source}\n{error:?}"));
    assert_eq!(theorems, 3, "{source}");
    refused(
        "def myAdd (a b : Nat) : Nat := Nat.add a b\n\
         macro \"dbl \" x:term:max : term => `(myAdd $x $x)\n\
         theorem t : dbl (3 : Nat) = 7 := rfl\n",
    );
}

/// A macro's names are not prechecked (the pin accepts an unused `nope`, and refuses it where
/// it is used), and they are pre-resolved where the macro is declared (the pin refuses `X = 2`:
/// `X` is `A.foo`).
#[test]
fn macro_names_are_resolved_where_declared_and_checked_where_used() {
    accepted("macro \"foo\" : term => `(nope)\ntheorem x : True := True.intro\n");
    refused("macro \"use_foo\" : term => `(nope)\ntheorem x : use_foo = 1 := rfl\n");
    refused(
        "namespace A\ndef foo : Nat := 1\nmacro \"X\" : term => `(foo)\nend A\n\
         def foo : Nat := 2\ntheorem t : X = 2 := rfl\n",
    );
}

/// The pin tries a kind's rules newest first: here the second `macro_rules` gives 6 and the pin
/// accepts. One rule per kind is kept here, so the second removes the first and the use is
/// refused rather than read by the older rule (which would give 4).
#[test]
fn a_second_rule_for_one_kind_is_refused_not_read_by_the_first() {
    refused(
        "def myAdd (a b : Nat) : Nat := Nat.add a b\nsyntax \"trip \" term:max : term\n\
         macro_rules | `(trip $x) => `(myAdd $x $x)\n\
         macro_rules | `(trip $x) => `(myAdd $x (myAdd $x $x))\n\
         theorem v : trip (2 : Nat) = 6 := rfl\n",
    );
}
