//! Saved-position checks must follow their owning grammar production.
#![forbid(unsafe_code)]
use fln_parse::{command_scope, parse_source_command};

#[test]
fn variable_binders_must_start_right_of_the_command() {
    for source in [
        "variable (x : Nat)\n(y : Nat)",
        "  variable (x : Nat)\n  (y : Nat)",
    ] {
        assert!(command_scope::parse(source.as_bytes()).is_err(), "{source}");
    }
    for source in [
        "variable (x : Nat)\n  (y : Nat)",
        "variable (x :\nNat)",
        "  variable (x : Nat)\n    (y : Nat)",
    ] {
        assert!(command_scope::parse(source.as_bytes()).is_ok(), "{source}");
    }
}
#[test]
fn named_and_goal_locations_must_start_right_of_at_not_the_tactic() {
    for location in ["h", "⊢", "|-"] {
        let source = format!("theorem t : True := by\n  simp only [] at\n    {location}");
        assert!(parse_source_command(source.as_bytes()).is_err(), "{source}");
        let source =
            format!("theorem t : True := by\n  simp only [] at\n                 {location}");
        assert!(parse_source_command(source.as_bytes()).is_ok(), "{source}");
    }
}
#[test]
fn wildcard_location_has_no_column_guard_in_the_reference_grammar() {
    let source = "theorem t : True := by\n  simp only [] at\n    *";
    assert!(parse_source_command(source.as_bytes()).is_ok(), "{source}");
}

#[test]
fn each_location_uses_the_same_anchor_and_retains_original_error_offsets() {
    let line = "  simp only [] /- 😀 -/ at h";
    let col = line
        .find("at h")
        .map(|i| line[..i].chars().count())
        .unwrap();
    for (delta, accepts) in [(0, false), (1, true)] {
        let source = format!(
            "theorem t : True := by\r\n{line}\r\n{}«h₂»",
            " ".repeat(col + delta)
        );
        let parsed = parse_source_command(source.as_bytes());
        assert_eq!(parsed.is_ok(), accepts, "{source}: {parsed:?}");
        if accepts {
            assert_eq!(parsed.unwrap().reconstruct_original(), source.as_bytes());
        } else {
            assert_eq!(
                parsed.unwrap_err().primary_offset().unwrap().0,
                source.find("«h₂»").unwrap()
            );
        }
    }
}

#[test]
fn binder_columns_use_scalar_positions_and_bracket_interiors_are_unrestricted() {
    let line = "/- 😀 -/ variable (x : Nat)";
    let col = line[..line.find("variable").unwrap()].chars().count();
    for (delta, accepts) in [(0, false), (1, true)] {
        let source = format!("{line}\r\n{}(y :\r\nNat)", " ".repeat(col + delta));
        assert_eq!(
            command_scope::parse(source.as_bytes()).is_ok(),
            accepts,
            "{source}"
        );
    }
    let source = "variable (x : Nat) in\ntheorem keep : x = x := by rfl";
    assert!(command_scope::parse(source.as_bytes()).is_ok());
}

#[test]
fn all_supported_location_tactics_apply_the_boundary() {
    for tactic in [
        "rw [h]",
        "erw [h]",
        "simp only []",
        "dsimp only []",
        "change True",
        "unfold f",
        "generalize h : x = y",
    ] {
        let line = format!("  {tactic} at");
        let at = line.len() - 2;
        for (column, accepts) in [(at, false), (at + 1, true)] {
            let source = format!("theorem t : True := by\n{line}\n{}hx", " ".repeat(column));
            assert_eq!(
                parse_source_command(source.as_bytes()).is_ok(),
                accepts,
                "{source}"
            );
        }
    }
}

#[test]
fn scoped_layout_verdicts_agree_with_the_actual_pinned_compiler() {
    use std::path::PathBuf;
    use std::process::Command;
    const LOCK: &str = include_str!("../../../SUITE.lock");
    let pin = LOCK
        .lines()
        .find(|line| line.starts_with("reference leanprover/lean4 "))
        .expect("reference pin");
    let field = |key: &str| {
        pin.split_whitespace()
            .find_map(|word| word.strip_prefix(key))
            .unwrap()
    };
    let tag = field("tag=");
    let commit = field("commit=");
    let library = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home)
                    .join(".elan/toolchains")
                    .join(format!("leanprover--lean4---{tag}"))
                    .join("lib/lean")
            })
        });
    let reference = library.as_ref().and_then(|library| {
        let binary = library.parent()?.parent()?.join("bin/lean");
        (binary.is_file() && library.join("Init.olean").is_file()).then_some(binary)
    });
    let Some(reference) = reference else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Lean compiler and library required"
        );
        eprintln!("SKIP: scoped-layout differential requires the pinned compiler and library");
        return;
    };
    let version = Command::new(&reference).arg("--version").output().unwrap();
    let version_text = String::from_utf8(version.stdout).unwrap();
    assert!(
        version.status.success()
            && version_text.contains(tag.trim_start_matches('v'))
            && version_text.contains(commit),
        "{version_text}"
    );
    let root = std::env::temp_dir().join(format!(
        "fln-scoped-layout-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir(&root).unwrap();
    let mut cases = Vec::new();
    for (indent, valid) in [("", false), ("  ", true)] {
        cases.push((
            format!("variable-{valid}"),
            format!("variable (x : Nat)\n{indent}(y : Nat)\n#check x\n#check y\n"),
            valid,
        ));
    }
    cases.push((
        "binder-interior".into(),
        "variable (x :\nNat)\n#check x\n".into(),
        true,
    ));
    for marker in ["h", "⊢", "|-"] {
        for valid in [false, true] {
            let tactic = "  rw [Nat.add_zero] at";
            let column = tactic.len() - 2 + usize::from(valid);
            let header = if marker == "h" {
                "theorem t (n : Nat) (h : n + 0 = 0) : n = 0 := by"
            } else {
                "theorem t (n : Nat) : n + 0 = n := by"
            };
            let finish = if marker == "h" { "\n  exact h" } else { "" };
            cases.push((
                format!("location-{}-{valid}", cases.len()),
                format!(
                    "{header}\n{tactic}\n{}{marker}{finish}\n",
                    " ".repeat(column)
                ),
                valid,
            ));
        }
    }
    cases.push((
        "wildcard".into(),
        "theorem t (n : Nat) : n + 0 = n := by\n  simp only [Nat.add_zero] at\n    *\n".into(),
        true,
    ));
    for (label, source, expected) in cases {
        let path = root.join(format!("{label}.lean"));
        std::fs::write(&path, &source).unwrap();
        let output = Command::new(&reference)
            .arg(&path)
            .env("LEAN_PATH", library.as_ref().unwrap())
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            Some(if expected { 0 } else { 1 }),
            "{label}: {}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        let native = command_scope::partition(source.as_bytes()).is_ok_and(|commands| {
            commands
                .into_iter()
                .all(|(_, bytes)| match command_scope::parse(bytes) {
                    Ok(Some(_)) => true,
                    Ok(None) => parse_source_command(bytes).is_ok(),
                    Err(_) => false,
                })
        });
        assert_eq!(native, expected, "native {label}: {source}");
        eprintln!(
            "{label}: reference={}, native_parser={native}",
            output.status.code().unwrap()
        );
    }
}
