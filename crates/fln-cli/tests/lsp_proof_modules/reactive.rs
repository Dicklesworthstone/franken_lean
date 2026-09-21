#![forbid(unsafe_code)]

//! Reactive checks must reach installed binaries without touching the importer.
use super::*;

fn successes_for<'a>(messages: &'a [String], uri: &str) -> Vec<&'a str> {
    successes(messages).into_iter().filter(|m| m.contains(&q(uri))).collect()
}
fn response_index(messages: &[String], id: usize) -> usize {
    messages.iter().position(|m| m.contains(&format!("\"id\":{id},"))).unwrap()
}

#[test]
fn both_servers_recheck_and_repair_importers_before_the_next_request() {
    for (binary, args) in [(env!("CARGO_BIN_EXE_fln"), &["serve-lsp"][..]), (env!("CARGO_BIN_EXE_lean"), &["--server"][..])] {
        let root = scratch();
        let lib = uri(&root.join("Lib.lean"));
        let main = uri(&root.join("Main.lean"));
        let messages = run(binary, args, &[
            open(&lib, "def value := 0"),
            open(&main, "import Lib\ntheorem use : value = 0 := by rfl"),
            change(&lib, 2, "def value := 1"), wait(&main, 1, 71),
            change(&lib, 3, "def value := 0"), wait(&main, 1, 72),
        ]);
        assert_eq!(errors(&messages, &main).len(), 1, "{messages:#?}");
        assert_eq!(successes_for(&messages, &main).len(), 2, "{messages:#?}");
        let failure = messages.iter().position(|m| m.contains("publishDiagnostics") && m.contains(&q(&main)) && m.contains("\"diagnostics\":[{")).unwrap();
        assert!(failure < response_index(&messages, 71));
        let repaired = messages.iter().rposition(|m| m.contains("sourceCheck") && m.contains(&q(&main))).unwrap();
        assert!(response_index(&messages, 71) < repaired && repaired < response_index(&messages, 72));
        assert!(messages[response_index(&messages, 72)].contains("\"result\":{}"));
    }
}

#[test]
fn transitive_diamond_consumers_refresh_once_without_rechecking_unrelated_files() {
    let root = scratch();
    let base = uri(&root.join("Base.lean"));
    let left = uri(&root.join("Left.lean"));
    let right = uri(&root.join("Right.lean"));
    let main = uri(&root.join("Main.lean"));
    let other = uri(&root.join("Other.lean"));
    let messages = fln(&[
        open(&base, "def value := 0"),
        open(&left, "import Base\ndef left := value"),
        open(&right, "import Base\ndef right := value"),
        open(&main, "import Left Right\ntheorem fixed : left = right := by rfl"),
        open(&other, "def unrelated := 7"),
        change(&base, 2, "def value := 1"),
    ]);
    // Opening Right/Main/Other does not affect the earlier independent files.
    for dependent in [&left, &right, &main] {
        assert_eq!(successes_for(&messages, dependent).len(), 2, "{messages:#?}");
        assert!(errors(&messages, dependent).is_empty(), "{messages:#?}");
    }
    assert_eq!(successes_for(&messages, &other).len(), 1, "{messages:#?}");
    let refreshed: Vec<_> = successes(&messages).into_iter().rev().take(4).collect();
    assert!(refreshed[0].contains(&q(&right)));
    assert!(refreshed[1].contains(&q(&main)));
    assert!(refreshed[2].contains(&q(&left)));
    assert!(refreshed[3].contains(&q(&base)));
}

#[test]
fn opening_a_previously_missing_import_repairs_its_waiting_consumer() {
    let root = scratch();
    let lib = uri(&root.join("New.lean"));
    let main = uri(&root.join("Main.lean"));
    let messages = fln(&[
        open(&main, "import New\ntheorem use : value = 7 := by rfl"),
        open(&lib, "def value := 7"), wait(&main, 1, 73),
    ]);
    assert_eq!(errors(&messages, &main).len(), 1, "{messages:#?}");
    assert_eq!(successes_for(&messages, &main).len(), 1, "{messages:#?}");
    assert!(!root.join("New.lean").exists());
    assert!(messages[response_index(&messages, 73)].contains("\"result\":{}"));
}

#[test]
fn invalidated_dependency_fails_same_version_waits_and_full_save_repairs_them_automatically() {
    let root = scratch();
    std::fs::write(root.join("Lib.lean"), "def value := 0").unwrap();
    let lib = uri(&root.join("Lib.lean"));
    let main = uri(&root.join("Main.lean"));
    let messages = fln(&[
        open(&lib, "def value := 0"), open(&main, "import Lib\ntheorem use : value = 0 := by rfl"),
        notify("textDocument/didChange", format!("{{\"textDocument\":{{\"uri\":{},\"version\":2}},\"contentChanges\":false}}", q(&lib))),
        wait(&main, 1, 74),
        notify("textDocument/didSave", format!("{{\"textDocument\":{{\"uri\":{}}},\"text\":\"def value := 0\"}}", q(&lib))),
        wait(&main, 1, 75),
    ]);
    assert!(messages[response_index(&messages, 74)].contains("\"error\""), "{messages:#?}");
    assert!(messages[response_index(&messages, 75)].contains("\"result\":{}"), "{messages:#?}");
    assert!(messages.iter().any(|m| m.contains("disk fallback is forbidden")));
    assert_eq!(successes_for(&messages, &main).len(), 2, "{messages:#?}");
}

#[test]
fn closing_and_reopening_a_dependency_switches_consumers_between_disk_and_overlay() {
    let root = scratch();
    std::fs::write(root.join("Lib.lean"), "def value := 1").unwrap();
    let lib = uri(&root.join("Lib.lean"));
    let main = uri(&root.join("Main.lean"));
    let messages = fln(&[
        open(&lib, "def value := 0"), open(&main, "import Lib\ntheorem use : value = 0 := by rfl"),
        document("textDocument/didClose", &lib), wait(&main, 1, 76),
        open(&lib, "def value := 0"), wait(&main, 1, 77),
    ]);
    assert_eq!(errors(&messages, &main).len(), 1, "{messages:#?}");
    assert_eq!(successes_for(&messages, &main).len(), 2, "{messages:#?}");
    assert_eq!(std::fs::read_to_string(root.join("Lib.lean")).unwrap(), "def value := 1");
}

#[test]
fn removed_imports_and_stale_dependency_messages_do_not_schedule_spurious_checks() {
    let root = scratch();
    let lib = uri(&root.join("Lib.lean"));
    let main = uri(&root.join("Main.lean"));
    let messages = fln(&[
        open(&lib, "def value := 0"), open(&main, "import Lib\ntheorem use : value = 0 := by rfl"),
        change(&lib, 2, "def value := 0"),
        notify("textDocument/didChange", format!("{{\"textDocument\":{{\"uri\":{},\"version\":1}},\"contentChanges\":false}}", q(&lib))),
        change(&main, 2, "theorem independent : (0 : Nat) = 0 := by rfl"),
        change(&lib, 3, "def value := 9"),
    ]);
    assert_eq!(successes_for(&messages, &main).len(), 3, "{messages:#?}");
    assert!(errors(&messages, &main).is_empty());
}

#[test]
fn structural_quoted_names_and_equivalent_file_uri_spellings_keep_dependency_identity() {
    let root = scratch();
    std::fs::write(root.join("Quoted.Library.lean"), "def value := 0").unwrap();
    let lib = uri(&root.join("Quoted.Library.lean")).replacen("file://", "file://localhost", 1);
    let main = uri(&root.join("Main.lean"));
    let messages = fln(&[
        open(&main, "import «Quoted.Library»\ntheorem use : value = 0 := by rfl"),
        open(&lib, "def value := 1"), change(&lib, 2, "def value := 0"),
    ]);
    assert_eq!(errors(&messages, &main).len(), 1, "{messages:#?}");
    assert_eq!(successes_for(&messages, &main).len(), 2, "{messages:#?}");
}

#[test]
fn rechecking_an_unchanged_importer_version_does_not_satisfy_future_version_waits() {
    let root = scratch();
    let lib = uri(&root.join("Lib.lean"));
    let main = uri(&root.join("Main.lean"));
    let source = "import Lib\ntheorem use : value = 0 := by rfl";
    let messages = fln(&[
        open(&lib, "def value := 0"), open(&main, source), wait(&main, 2, 78),
        change(&lib, 2, "def value := 0"), wait(&main, 1, 79), change(&main, 2, source),
    ]);
    assert!(response_index(&messages, 79) < response_index(&messages, 78), "{messages:#?}");
    assert!(messages[response_index(&messages, 78)].contains("\"result\":{}"));
}
