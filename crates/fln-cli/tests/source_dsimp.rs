//! Installed command and library admission consume exactly the same fixtures.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn installed_dsimp_accepts_and_refuses_the_shared_programs_without_changing_source() {
    let dir = std::env::temp_dir().join(format!("fln-dsimp-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("Proof.lean");
    let mut failures = Vec::new();
    let mut cases = 0;
    for case in include_str!("../../fln/tests/source_dsimp.lean").split("-- CASE ").skip(1) {
        let (header, source) = case.split_once('\n').unwrap();
        let (name, verdict) = header.split_once(' ').unwrap();
        assert!(matches!(verdict, "accept" | "reject"));
        std::fs::write(&path, source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"]).arg(&path).output().unwrap();
        if output.status.success() != (verdict == "accept") {
            failures.push(format!("{name}: {}\n{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr)));
        }
        assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
        cases += 1;
    }
    assert_eq!(cases, 26);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
