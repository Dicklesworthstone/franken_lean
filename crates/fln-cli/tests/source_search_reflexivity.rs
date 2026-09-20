//! Installed proof-search arithmetic succeeds only with an authoritative receipt.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn installed_search_reports_checked_arithmetic_rejection_and_resource_stops() {
    let directory =
        std::env::temp_dir().join(format!("fln-search-reflexivity-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let path = directory.join("source.lean");
    for (source, status) in [
        (
            "theorem arithmetic : 2 + 3 = 5 := by solve_by_elim\ntheorem heterogeneous : HEq (2 + 3) 5 := by solve_by_elim\n",
            0,
        ),
        (
            "def preceding : Nat := 7\ntheorem bad : 2 + 3 = 6 := by solve_by_elim\n",
            1,
        ),
        (
            "theorem exhausted : (1 <<< 18446744073709551616) = 0 := by solve_by_elim\n",
            3,
        ),
        (
            "theorem premise (p : Prop) (rule : 2 + 3 = 5 -> p) : p := by solve_by_elim\ntheorem recovered : True := by solve_by_elim\n",
            0,
        ),
    ] {
        std::fs::write(&path, source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&path)
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            Some(status),
            "{source}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if status == 0 {
            assert!(output.stderr.is_empty());
            let json = String::from_utf8(output.stdout).unwrap();
            for field in [
                "\"authority\":true",
                "\"outcome\":\"complete\"",
                "\"theorems\":2",
                "\"executed\":false",
            ] {
                assert!(json.contains(field), "{json}");
            }
        } else {
            assert!(output.stdout.is_empty());
            let json = String::from_utf8(output.stderr).unwrap();
            assert!(json.contains("\"authority\":false"), "{json}");
            if status == 3 {
                assert!(json.contains("\"outcome\":\"inconclusive\""), "{json}");
            }
        }
        assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
    }
}
