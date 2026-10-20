//! The installed source runner resolves List append through ordinary instances.
#![forbid(unsafe_code)]
use std::{
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn path(text: &str) -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-list-dictionary-{}-{}.lean",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, text).unwrap();
    path
}
fn run(text: &str, success: bool) -> String {
    let out = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json"])
        .arg(path(text))
        .output()
        .unwrap();
    assert_eq!(out.status.success(), success, "{out:?}");
    String::from_utf8(if success { out.stdout } else { out.stderr }).unwrap()
}
#[test]
fn polymorphic_append_retains_the_real_selected_dictionary() {
    let out = run(
        "def join {A : Type} (xs ys : List A) : List A := xs ++ ys\n#eval join [1,2,3] [4,5]\n#eval ([\"a\"] : List String) ++ [\"b\"]\n#eval \"left\" ++ \"right\"",
        true,
    );
    for expected in ["[1,2,3,4,5]", "[\"a\",\"b\"]", "leftright"] {
        assert!(out.contains(expected), "{out}");
    }
    let custom = run(
        "local instance : Append (List Nat) := ⟨fun xs ys => ys⟩\n#eval ([1] : List Nat) ++ [2]",
        true,
    );
    assert!(custom.contains("\"finalValue\":[2]"), "{custom}");
}
#[test]
fn missing_instances_are_not_replaced_with_a_builtin_operator() {
    run("#eval true ++ false", false);
    run("#eval ([1] : List Nat) ++ ([\"bad\"] : List String)", false);
}
#[test]
fn explicit_empty_prelude_keeps_its_own_environment() {
    let out = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(path("prelude\ndef t : List Nat := []"))
        .output()
        .unwrap();
    assert!(!out.status.success(), "{out:?}");
}
