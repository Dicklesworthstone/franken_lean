//! Alias-aware selective namespace opens and re-exports use the ordinary
//! checked source path. No declarations are copied to make an alias resolve.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn engine() -> Engine {
    Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap()
}

fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}

fn accepted(source: &str) {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let result = base
        .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
        .unwrap_or_else(|error| panic!("{source}: {error}"))
        .into_complete()
        .expect("complete checked source");
    assert!(result.theorems > 0);
    assert_eq!(base.logical_root(&KVMap::new()), root);
}

#[test]
fn selective_open_reads_exported_aliases_and_reexport_keeps_the_original_target() {
    accepted(
        "namespace Original\ndef x : Nat := 7\nend Original\n\
         namespace View\nexport Original (x)\nend View\n\
         open View (x)\ntheorem selected : x = 7 := rfl\n\
         namespace Again\nexport View (x)\nend Again\n\
         theorem reexported : Again.x = 7 := rfl\n",
    );
}

#[test]
fn exact_members_outrank_aliases_and_explicit_protected_members_are_available() {
    accepted(
        "namespace Original\nprotected def x : Nat := 7\n\
         def «with.dot» : Nat := 8\nend Original\n\
         namespace View\ndef x : Nat := 9\nexport Original (x «with.dot»)\nend View\n\
         open View (x «with.dot»)\n\
         theorem exactWins : x = 9 := rfl\n\
         theorem escaped : «with.dot» = 8 := rfl\n\
         namespace Protected\nexport Original (x)\nend Protected\n\
         theorem explicitProtected : Protected.x = 7 := rfl\n",
    );
}

#[test]
fn a_namespace_without_the_member_does_not_mask_an_alias_in_another_namespace() {
    accepted(
        "namespace Original\ndef x : Nat := 7\nend Original\n\
         namespace Left.View\nexport Original (x)\nend Left.View\n\
         namespace Right.View\ndef other : Nat := 9\nend Right.View\n\
         open Left Right\nopen View (x)\ntheorem found : x = 7 := rfl\n",
    );
}

#[test]
fn two_successful_namespace_resolutions_are_ambiguous_even_for_the_same_target() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let prefix = "namespace Original\ndef x : Nat := 7\nend Original\n\
        namespace Left.View\nexport Original (x)\nend Left.View\n\
        namespace Right.View\nexport Original (x)\nend Right.View\nopen Left Right\n";
    for command in ["open View (x)", "export View (x)"] {
        let source = format!("{prefix}{command}\n");
        let error = base
            .check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
            .expect_err("two namespaces cannot be silently deduplicated");
        assert!(error.to_string().contains("ambiguous"), "{error}");
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn a_late_unknown_member_publishes_nothing_and_a_clean_retry_recovers() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    let prefix = "namespace Original\ndef x : Nat := 7\nend Original\n\
        namespace View\nexport Original (x)\nend View\n";
    for command in ["open View (x missing)", "export View (x missing)"] {
        let source = format!("{prefix}{command}\n");
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err()
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
    accepted(&format!(
        "{prefix}open View (x)\ntheorem recovered : x = 7 := rfl\n"
    ));
}

#[test]
fn aliases_neither_create_namespaces_nor_prove_false_equalities() {
    let base = engine();
    let prefix = "namespace Original.Inner\ndef x : Nat := 7\nend Original.Inner\n\
        export Original (Inner.x)\n";
    for suffix in [
        "open Inner",
        "export Inner (x)",
        "theorem wrong : Inner.x = 8 := rfl",
    ] {
        let source = format!("{prefix}{suffix}\n");
        assert!(
            base.check_source_files(&[source.as_bytes()], &KVMap::new(), limits())
                .is_err(),
            "{source}"
        );
    }
    accepted(&format!("{prefix}theorem qualified : Inner.x = 7 := rfl\n"));
}
