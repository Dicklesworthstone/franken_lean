//! Standard append rules are checked library theorems, not a privileged simp path.
#![forbid(unsafe_code)]
use std::{
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn path(source: &str) -> PathBuf {
    let p = std::env::temp_dir().join(format!(
        "fln-list-simp-{}-{}.lean",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&p, source).unwrap();
    p
}
fn check(source: &str) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(path(source))
        .output()
        .unwrap()
}
fn good(source: &str) {
    let o = check(source);
    assert!(o.status.success(), "{o:?}");
    assert!(
        String::from_utf8(o.stdout)
            .unwrap()
            .contains("\"axioms\":0,\"sorryDeclarations\":0")
    );
}
fn bad(source: &str) {
    let o = check(source);
    assert!(!o.status.success(), "{o:?}");
    assert!(o.stdout.is_empty(), "{o:?}");
}
#[test]
fn default_append_rules_work_on_abstract_polymorphic_lists_and_under_binders() {
    good(
        "universe u\n\
      theorem original (xs : List Nat) : xs ++ [] = xs := by simp\n\
      theorem both {A : Type u} (xs : List A) : [] ++ (xs ++ []) = xs := by simp\n\
      theorem assoc {A : Type u} (xs ys zs : List A) : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by simp\n\
      theorem quantified {A : Type u} : ∀ xs : List A, xs ++ [] = xs := by intro xs; simp\n\
      theorem local_use (xs : List String) (h : xs ++ [] = []) : xs = [] := by simpa using h\n",
    );
}
#[test]
fn explicit_selection_erasure_and_scoped_rules_still_control_simplification() {
    good("theorem explicit (xs : List Nat) : xs ++ [] = xs := by simp only [List.append_nil]");
    bad("theorem missing (xs : List Nat) : xs ++ [] = xs := by simp only []");
    bad("theorem erased (xs : List Nat) : xs ++ [] = xs := by simp [-List.append_nil]");
    bad(
        "attribute [-simp] List.append_nil\ntheorem erased (xs : List Nat) : xs ++ [] = xs := by simp",
    );
    good(
        "attribute [-simp] List.append_nil\nattribute [simp] List.append_nil\ntheorem restored (xs : List Nat) : xs ++ [] = xs := by simp",
    );
}
#[test]
fn a_local_append_dictionary_cannot_inherit_the_standard_lists_laws() {
    bad("local instance : Append (List Nat) := ⟨fun xs ys => ys⟩\n\
         theorem false_rule : ([1] : List Nat) ++ [] = [1] := by simp");
    good(
        "local instance : Append (List Nat) := ⟨fun xs ys => ys⟩\n\
          theorem actual (xs ys : List Nat) : xs ++ ys = ys := by rfl",
    );
    bad("theorem false_rule (xs ys : List Nat) : xs ++ ys = xs := by simp");
}
#[test]
fn explicit_prelude_cannot_obtain_hidden_library_declarations() {
    let o = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(path("prelude\n#check List.append_nil"))
        .output()
        .unwrap();
    assert!(!o.status.success(), "{o:?}");
}
