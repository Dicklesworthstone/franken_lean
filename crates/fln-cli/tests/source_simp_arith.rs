//! `simp +arith` over `Nat` (vendored `Lean/Meta/Tactic/Simp/Arith/Nat/*.lean`, the `simpArith`
//! post step of `Lean/Meta/Tactic/Simp/Rewrite.lean:303`): linear constraints and terms are
//! normalized by reflection over `Init/Data/Nat/Linear.lean`, so every rewrite is a
//! `Nat.Linear.*` proof the kernel decides. Through `fln check-source` over `prelude` +
//! `Init.Data.Nat.Linear`. Every program here was run through the pinned `lean` v4.32.0 with
//! the same header first (2026-10-23), with the verdict recorded below, and is compared with
//! the pinned binary again when it is present. The normal forms are the pin's: each
//! `guard_target =ₛ` and `guard_hyp … :ₛ` below holds there.
#![forbid(unsafe_code)]
#[path = "source_simp_arith/int.rs"]
mod int;

use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Data.Nat.Linear\nimport Init.Guard\n";

/// Accepted at the pin and here.
const ACCEPTED: &[(&str, &str)] = &[
    // `tests/elab/1236.lean`.
    (
        "scaled_side",
        "example (x : Nat) : x ≤ x * 2 := by simp +arith\n",
    ),
    (
        "offsets",
        "example (x : Nat) : x + 1 ≤ x + 2 := by simp +arith\n",
    ),
    (
        "doubling",
        "example (x : Nat) : 2 * x = x + x := by simp +arith\n",
    ),
    // `tests/elab/simpArith1.lean`'s `ex1`, through the structure-instance configuration.
    (
        "configuration_structure",
        "example (a b c : Nat) : a + b < b + 1 + a + c := by\n  simp (config := { arith := true })\n",
    ),
    // `tests/elab/simpCnstr1.lean`: normalized, not closed, then finished by `exact`.
    (
        "normal_form_left_open",
        "example (a b : Nat) (h : a ≤ 2) : a + b + 1 + a < b + 4 + a := by\n  simp +arith\n  \
         guard_target =ₛ a ≤ 2\n  exact h\n",
    ),
    (
        "negated_constraint",
        "example (a b : Nat) (h : 3 ≤ a) : ¬ (a + b + 1 + a < b + 4 + a) := by\n  simp +arith\n  \
         guard_target =ₛ 3 ≤ a\n  exact h\n",
    ),
    (
        "unsatisfiable_goal",
        "example (a : Nat) (h : False) : 4 = 8 + a := by\n  simp +arith\n  guard_target =ₛ False\n  \
         exact h\n",
    ),
    // `tests/elab/simp_nat_arith.lean`.
    (
        "terms_under_a_function",
        "example (f : Nat → Nat) (x y : Nat) : f (2*x + y) = f (y + x + x) := by\n  simp +arith\n",
    ),
    (
        "both_sides_of_an_iff",
        "example (x y : Nat) : (2*x + y = 4) ↔ (y + x + x = 4) := by\n  simp +arith\n",
    ),
    // `tests/elab/simpArithCacheIssue.lean`: `simp +arith only` normalizes the maximal terms.
    (
        "only_maximal_terms",
        "example (x y : Nat) (h : y = 0) : id ((x + x) + y) = id (x + x) := by\n  simp +arith only\n  \
         guard_target =ₛ id (2 * x + y) = id (2 * x)\n  simp [h]\n",
    ),
    // `tests/elab/simpArith1.lean`'s `ex5` and `ex6`: a hypothesis normalized to `False`
    // closes the goal; one normalized otherwise is rewritten in place.
    (
        "hypothesis_to_false",
        "theorem ex5 (a b c d : Nat) (h : a + d + b > b + 1 + (a + (c + c) + d)) : False := by\n  \
         simp +arith at h\n",
    ),
    (
        "hypothesis_rewritten",
        "theorem ex6 (a b : Nat) (p : Nat → Prop) (h : p (a + 1 + a + 2 + b)) : p (2*a + b + 3) := by\n  \
         simp +arith at h\n  guard_hyp h :ₛ p (2 * a + b + 3)\n  assumption\n",
    ),
];

/// Rejected at the pin and here.
const REJECTED: &[(&str, &str)] = &[
    // Already normal: "`simp` made no progress".
    (
        "no_progress",
        "example (x : Nat) : x ≤ 3 := by simp +arith\n",
    ),
    // Not the pin's normal form.
    (
        "other_normal_form",
        "example (a b : Nat) (h : a ≤ 2) : a + b + 1 + a < b + 4 + a := by\n  simp +arith\n  \
         guard_target =ₛ a + 1 ≤ 3\n  exact h\n",
    ),
];

/// Refused here as unsupported: a configuration field this engine does not honour, set away
/// from its default (`source_simp_config.rs` reads the slot as a whole).
const REFUSED: &[(&str, &str, &str)] = &[(
    "other_configuration",
    "example (x : Nat) : x + 0 = x := by simp (config := { zeta := false })\n",
    "expected default simplification configuration",
)];

fn pinned_lib() -> Option<PathBuf> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home)
                    .join(".elan/toolchains")
                    .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                    .join("lib/lean")
            })
        })
        .filter(|lib| lib.join("Init/Data/Nat/Linear.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "the pinned Reference library is required"
    );
    if lib.is_none() {
        eprintln!("SKIP: pinned Reference lib/lean absent");
    }
    lib
}

fn workspace() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-simp-arith-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// `fln check-source` on `HEADER` + `program`, and the pinned binary's exit code when present.
fn check(lib: &Path, root: &Path, name: &str, program: &str) -> (i32, String, Option<i32>) {
    check_with_header(lib, root, name, HEADER, program)
}

fn check_with_header(
    lib: &Path,
    root: &Path,
    name: &str,
    header: &str,
    program: &str,
) -> (i32, String, Option<i32>) {
    let entry = root.join(format!("{name}.lean"));
    std::fs::write(&entry, format!("{header}{program}")).unwrap();
    let theirs = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|lean| lean.is_file())
        .map(|pinned| {
            Command::new(pinned)
                .arg(&entry)
                .env("LEAN_PATH", lib)
                .output()
                .expect("run the pinned lean")
                .status
                .code()
                .expect("normal pinned exit")
        });
    let ours = Command::new(env!("CARGO_BIN_EXE_fln"))
        .arg("check-source")
        .arg(&entry)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run the installed CLI");
    (
        ours.status.code().expect("normal process exit"),
        String::from_utf8_lossy(&ours.stderr).into_owned(),
        theirs,
    )
}

#[test]
fn simp_arith_normalizes_nat_linear_arithmetic_as_the_pin_does() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    // One workspace, so the import closure is admitted once for every program.
    let root = workspace();
    for (name, program) in ACCEPTED {
        let (code, stderr, pinned) = check(&lib, &root, name, program);
        assert_eq!(code, 0, "{name}: {program}\n{stderr}");
        assert_eq!(pinned.unwrap_or(0), 0, "{name}: the pinned lean rejects it");
    }
    for (name, program) in REJECTED {
        let (code, stderr, pinned) = check(&lib, &root, name, program);
        assert_ne!(code, 0, "{name}: accepted {program}");
        assert!(
            !stderr.contains("unexpected syntax"),
            "{name}: refused as unsupported, not rejected\n{stderr}"
        );
        assert_ne!(pinned.unwrap_or(1), 0, "{name}: the pinned lean accepts it");
    }
    for (name, program, refusal) in REFUSED {
        let (code, stderr, _) = check(&lib, &root, name, program);
        assert_ne!(code, 0, "{name}: accepted {program}");
        assert!(
            stderr.contains(refusal),
            "{name}: not the typed refusal\n{stderr}"
        );
    }
}

#[test]
fn simp_arith_identifies_defeq_atoms_in_nat_and_int_constraints() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let header =
        "prelude\nimport Init.Data.Nat.Linear\nimport Init.Data.Int.Linear\nimport Init.Guard\n";
    // The two applications are distinct syntax with the same head and proof-irrelevant
    // arguments. KExprMap must identify them before arithmetic can cancel their monomials.
    let accepted = "example (P : Prop) (f : P → Nat) (h1 h2 : P) (a b : Nat) (h : a ≤ b) :\n\
        f h1 + a ≤ f h2 + b := by\n  simp +arith only\n  guard_target =ₛ a ≤ b\n  exact h\n\
        example (P : Prop) (f : P → Int) (h1 h2 : P) (a b : Int) (h : a = b) :\n\
        f h1 + a = f h2 + b := by\n  simp +arith only\n  guard_target =ₛ a = b\n  exact h\n";
    let (code, stderr, pinned) = check_with_header(&lib, &root, "defeq_atoms", header, accepted);
    assert_eq!(pinned.unwrap_or(0), 0, "the pinned lean rejects it");
    assert_eq!(code, 0, "{accepted}\n{stderr}");

    for (name, program) in [
        (
            "distinct_nat_arguments",
            "example (f : Nat → Nat) (x y a b : Nat) (h : a ≤ b) :\n\
             f x + a ≤ f y + b := by\n  simp +arith only\n  exact h\n",
        ),
        (
            "distinct_int_heads",
            "example (P : Prop) (f g : P → Int) (h1 h2 : P) (a b : Int) (h : a = b) :\n\
             f h1 + a = g h2 + b := by\n  simp +arith only\n  exact h\n",
        ),
    ] {
        let (code, stderr, pinned) = check_with_header(&lib, &root, name, header, program);
        assert_ne!(pinned.unwrap_or(1), 0, "{name}: the pinned lean accepts it");
        assert_ne!(code, 0, "{name}: accepted {program}");
        assert!(
            !stderr.contains("unexpected syntax"),
            "{name}: refused as unsupported, not rejected\n{stderr}"
        );
    }
}

#[test]
fn simp_arith_recognizes_definitionally_equal_instances_without_assuming_custom_operations() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let header =
        "prelude\nimport Init.Data.Nat.Linear\nimport Init.Data.Int.Linear\nimport Init.Guard\n";
    // Instance definitions are implicit-reducible, not abbreviations. Exercise the
    // pin's isDefEqI fallback while keeping expected normal forms explicitly canonical.
    let accepted = [
        (
            "nonstandard_operations_remain_atoms",
            r#"instance customAdd : Add Nat := ⟨fun a _ => a⟩
example (x y a b : Nat) (h : a ≤ b) :
    Nat.add (@Add.add Nat customAdd x y) a ≤ Nat.add (@Add.add Nat customAdd x y) b := by
  simp +arith only
  guard_target =ₛ a ≤ b
  exact h
"#,
        ),
        (
            "nat_homogeneous_instances",
            r#"instance addAlias : Add Nat := instAddNat
instance mulAlias : Mul Nat := instMulNat
example (a b : Nat) (h : a ≤ b) :
    @Add.add Nat addAlias a 5 ≤ @Add.add Nat addAlias b 5 := by
  simp +arith only
  guard_target =ₛ a ≤ b
  exact h
example (a : Nat) : @Mul.mul Nat mulAlias 2 a = a + a := by
  simp +arith only
"#,
        ),
        (
            "nat_heterogeneous_instances",
            r#"instance addAlias : HAdd Nat Nat Nat := @instHAdd Nat instAddNat
instance mulAlias : HMul Nat Nat Nat := @instHMul Nat instMulNat
example (a : Nat) :
    @HMul.hMul Nat Nat Nat mulAlias 2 a = @HAdd.hAdd Nat Nat Nat addAlias a a := by
  simp +arith only
"#,
        ),
        (
            "nat_order_instances",
            r#"instance leAlias : LE Nat := instLENat
instance ltAlias : LT Nat := instLTNat
example (a b : Nat) (h : @LE.le Nat instLENat a b) :
    @LE.le Nat leAlias (Nat.add a 2) (Nat.add b 2) := by
  simp +arith only
  guard_target =ₛ @LE.le Nat instLENat a b
  exact h
example (a : Nat) : @LT.lt Nat ltAlias a (Nat.succ a) := by
  simp +arith only
"#,
        ),
        (
            "nat_numeral_instance",
            r#"instance numeralAlias : OfNat Nat 3 := instOfNatNat 3
example (a : Nat) (h : 6 = a) :
    Nat.add (@OfNat.ofNat Nat 3 numeralAlias) (@OfNat.ofNat Nat 3 numeralAlias) = a := by
  simp +arith only
  guard_target =ₛ 6 = a
  exact h
"#,
        ),
        (
            "int_homogeneous_instances",
            r#"instance addAlias : Add Int := Int.instAdd
instance subAlias : Sub Int := Int.instSub
instance mulAlias : Mul Int := Int.instMul
instance negAlias : Neg Int := Int.instNegInt
example (a : Int) : @Sub.sub Int subAlias (@Add.add Int addAlias a a) a = a := by
  simp +arith only
example (a : Int) : @Mul.mul Int mulAlias 2 a = @Add.add Int addAlias a a := by
  simp +arith only
example (a : Int) : @Neg.neg Int negAlias (@Neg.neg Int negAlias a) = a := by
  simp +arith only
"#,
        ),
        (
            "int_heterogeneous_instances",
            r#"instance addAlias : HAdd Int Int Int := @instHAdd Int Int.instAdd
instance subAlias : HSub Int Int Int := @instHSub Int Int.instSub
instance mulAlias : HMul Int Int Int := @instHMul Int Int.instMul
example (a : Int) :
    @HSub.hSub Int Int Int subAlias (@HAdd.hAdd Int Int Int addAlias a a) a = a := by
  simp +arith only
example (a : Int) :
    @HMul.hMul Int Int Int mulAlias 2 a = @HAdd.hAdd Int Int Int addAlias a a := by
  simp +arith only
"#,
        ),
        (
            "int_order_and_divisibility_instances",
            r#"instance leAlias : LE Int := Int.instLEInt
instance ltAlias : LT Int := Int.instLTInt
instance dvdAlias : Dvd Int := Int.instDvd
example (a : Int) : @LE.le Int leAlias a (Int.add a 2) := by
  simp +arith only
example (a : Int) : @LT.lt Int ltAlias a (Int.add a 1) := by
  simp +arith only
example (a : Int) (h : @Dvd.dvd Int Int.instDvd 2 (a + 3)) :
    @Dvd.dvd Int dvdAlias 4 (Int.add (Int.mul 2 a) 6) := by
  simp +arith only
  guard_target =ₛ @Dvd.dvd Int Int.instDvd 2 (a + 3)
  exact h
example (a : Int) : ¬ @LT.lt Int ltAlias (Int.add a 1) a := by
  simp +arith only
"#,
        ),
    ];
    for (name, program) in accepted {
        let (code, stderr, pinned) = check_with_header(&lib, &root, name, header, program);
        assert_eq!(pinned.unwrap_or(0), 0, "{name}: the pinned lean rejects it");
        assert_eq!(code, 0, "{name}: {program}\n{stderr}");
    }
    for (name, program) in [
        (
            "nonstandard_nat_addition",
            r#"instance wrongAdd : Add Nat := ⟨fun _ _ => 0⟩
example : @Add.add Nat wrongAdd 1 1 = 2 := by simp +arith only
"#,
        ),
        (
            "nonstandard_int_order",
            r#"instance wrongLE : LE Int := ⟨fun _ _ => False⟩
example : @LE.le Int wrongLE 0 1 := by simp +arith only
"#,
        ),
        (
            "irreducible_instance_alias",
            r#"@[irreducible] def hiddenAdd : Add Nat := instAddNat
example (a b : Nat) (h : a ≤ b) :
    @Add.add Nat hiddenAdd a 5 ≤ @Add.add Nat hiddenAdd b 5 := by
  simp +arith only
  exact h
"#,
        ),
    ] {
        let (code, stderr, pinned) = check_with_header(&lib, &root, name, header, program);
        assert_ne!(pinned.unwrap_or(1), 0, "{name}: the pinned lean accepts it");
        assert_ne!(code, 0, "{name}: accepted {program}");
        assert!(
            !stderr.contains("unexpected syntax"),
            "{name}: refused as unsupported, not rejected\n{stderr}"
        );
    }
}
