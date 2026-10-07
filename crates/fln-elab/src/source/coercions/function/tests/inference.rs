//! CoeFun determines open function domains/results in generic consumers.
use super::*;

#[test]
fn a_bundled_function_infers_a_polymorphic_consumer_domain() {
    let value = accepted(
        "def pass (W : Type) [inst : CoeFun W (fun _ => Nat -> Nat)] (w : W) (use : {A : Type} -> (A -> A) -> Nat) : Nat := use w",
    );
    assert!(contains(&value, "CoeFun.coe"));
}

#[test]
fn a_bundled_function_infers_an_open_codomain_without_changing_its_domain() {
    let value = accepted(
        "def pass (W : Type) [inst : CoeFun W (fun _ => Nat -> Nat)] (w : W) (use : {A : Type} -> (Nat -> A) -> Nat) : Nat := use w",
    );
    assert!(contains(&value, "CoeFun.coe"));
}

#[test]
fn ordinary_functions_remain_uncoerced_in_a_generic_consumer() {
    let value =
        accepted("def pass (f : Nat -> Nat) (use : {A : Type} -> (A -> A) -> Nat) : Nat := use f");
    assert!(!contains(&value, "CoeFun.coe"));
}

#[test]
fn missing_and_incompatible_dictionaries_do_not_invent_function_arguments() {
    let env = environment();
    for source in [
        "def bad (W : Type) (w : W) (use : {A : Type} -> (A -> A) -> Nat) : Nat := use w",
        "def bad (W : Type) [inst : CoeFun W (fun _ => Nat -> Nat)] (w : W) (use : {A : Type} -> ((Nat -> Nat) -> A) -> Nat) : Nat := use w",
        "def bad (W : Type) [inst : CoeFun W (fun _ => Nat)] (w : W) (use : {A : Type} -> (A -> A) -> Nat) : Nat := use w",
    ] {
        if let Ok(checked) = crate::check_definition_source(source.as_bytes(), &env, budget()) {
            assert!(
                !matches!(checked.outcome, Outcome::Complete(Verdict::Accepted { .. })),
                "{source}"
            );
        }
    }
}
