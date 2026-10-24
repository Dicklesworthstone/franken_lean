//! Real source proofs, checked by both engines. Syntactic guards pin the observable
//! integer normal forms; false and already-normal goals must remain rejected.
#![forbid(unsafe_code)]
use super::{check_with_header, pinned_lib, workspace};

const HEADER: &str =
    "prelude\nimport Init.Data.Nat.Linear\nimport Init.Data.Int.Linear\nimport Init.Guard\n";

const ACCEPTED: &[(&str, &str)] = &[
    (
        "commutativity_and_cancellation",
        "example (x : Int) : x + 1 = 1 + x := by simp +arith only\n\
         example (x y : Int) : x + y + 2 + y = y + 1 + 1 + x + y := by simp +arith only\n\
         example (x y : Int) : x + y - x + 2 - y + 1 = 3 := by simp +arith only\n",
    ),
    (
        "signed_terms_under_function",
        "example (f : Int → Int) (x y : Int) : f (x + y - x + (2 - y)*(-2) + 1) = f (3*y + -3) := by simp +arith only\n\
         example (f : Int → Int) (x y : Int) : f (-(x - y) + x) = f y := by simp +arith only\n\
         example (f : Int → Int) (x : Int) : f ((2 : Int)*x + (1 : Int)*x) = f (3*x) := by simp +arith only\n\
         example (f : Int → Int) (a b c d e : Int) : f (a+b+c+d+e) = f (e+d+c+b+a) := by simp +arith only\n",
    ),
    (
        "nonlinear_atoms",
        "example (x y : Int) : x*y + x*y = 2*(x*y) := by simp +arith only\n",
    ),
    (
        "unbounded_coefficients",
        "example (x : Int) : 18446744073709551617*x - 18446744073709551616*x = x := by simp +arith only\n",
    ),
    (
        "equation_variable",
        "example (x y : Int) (h : x = y) : 2*x = x + y := by\n  simp +arith only\n  guard_target =ₛ x = y\n  exact h\n",
    ),
    (
        "equation_constant",
        "example (x : Int) (h : x = -1) : 2*x + 1 = x := by\n  simp +arith only\n  guard_target =ₛ x = -1\n  exact h\n",
    ),
    (
        "equation_polynomial",
        "example (x y : Int) (h : 2*x + -3*y + -1 = 0) : 2*x = 3*y + 1 := by\n  simp +arith only\n  guard_target =ₛ 2*x + -3*y + -1 = 0\n  exact h\n",
    ),
    (
        "equation_gcd",
        "example (x y : Int) (h : x + -2*y + -3 = 0) : 2*x = 4*y + 6 := by\n  simp +arith only\n  guard_target =ₛ x + -2*y + -3 = 0\n  exact h\n",
    ),
    (
        "impossible_equations",
        "example (x : Int) (h : 2*x = 1) : False := by simp +arith only at h\n\
         example (x : Int) (h : False) : x + 1 = x := by\n  simp +arith only\n  guard_target =ₛ False\n  exact h\n",
    ),
    (
        "valid_orders",
        "example (x : Int) : x - 1 < x := by simp +arith only\n\
         example (x : Int) : x > x - 1 := by simp +arith only\n\
         example (x y : Int) : x + y + 2 + y ≤ y + 1 + 1 + x + y := by simp +arith only\n",
    ),
    (
        "impossible_order_hypotheses",
        "example (x y : Int) (h : x + y + 2 + y < y + 1 + 1 + x + y) : False := by simp +arith only at h\n\
         example (x y : Int) (h : x + y + 2 + y > y + 1 + 1 + x + y) : False := by simp +arith only at h\n",
    ),
    (
        "order_hypothesis_normal_form",
        "example (x y : Int) (h : 6*x + y + 3 + y + 1 < y + 1 + 1 + x + 5*y) : 5*x + -4*y + 3 ≤ 0 := by\n  simp +arith only at h\n  guard_hyp h :ₛ 5*x + -4*y + 3 ≤ 0\n  exact h\n",
    ),
    (
        "order_gcd_exact",
        "example (x : Int) (h : x + -2 ≤ 0) : 6*x ≤ 12 := by\n  simp +arith only\n  guard_target =ₛ x + -2 ≤ 0\n  exact h\n",
    ),
    (
        "order_tightening_negative_offset",
        "example (x : Int) (h : x ≤ 0) : 6*x + 4 ≤ 9 := by\n  simp +arith only\n  guard_target =ₛ x ≤ 0\n  exact h\n",
    ),
    (
        "order_tightening_positive_offset",
        "example (x : Int) (h : x + 1 ≤ 0) : 6*x + 4 ≤ 2 := by\n  simp +arith only\n  guard_target =ₛ x + 1 ≤ 0\n  exact h\n\
         example (x : Int) (h : -1*x + 1 ≤ 0) : (-6)*x + 4 ≤ 2 := by\n  simp +arith only\n  guard_target =ₛ -1*x + 1 ≤ 0\n  exact h\n",
    ),
    (
        "negated_orders",
        "example (x : Int) (h : x + 1 ≤ 0) : ¬ (0 ≤ x) := by\n  simp +arith only\n  guard_target =ₛ x + 1 ≤ 0\n  exact h\n\
         example (x : Int) (h : x + 1 ≤ 0) : ¬ (x ≥ 0) := by\n  simp +arith only\n  guard_target =ₛ x + 1 ≤ 0\n  exact h\n\
         example (x : Int) (h : -1*x ≤ 0) : ¬ (x < 0) := by\n  simp +arith only\n  guard_target =ₛ -1*x ≤ 0\n  exact h\n\
         example (x : Int) (h : -1*x ≤ 0) : ¬ (0 > x) := by\n  simp +arith only\n  guard_target =ₛ -1*x ≤ 0\n  exact h\n",
    ),
    (
        "divisibility_normal_form",
        "example (x : Int) (h : (2 : Int) ∣ 3*x) : (2 : Int) ∣ (2*x + x) := by\n  simp +arith only\n  guard_target =ₛ 2 ∣ 3*x\n  exact h\n",
    ),
    (
        "divisibility_gcd",
        "example (x y : Int) (h : (3 : Int) ∣ (2*x + y + 4)) : (6 : Int) ∣ (4*x + 2*y + 8) := by\n  simp +arith only\n  guard_target =ₛ 3 ∣ (2*x + y + 4)\n  exact h\n",
    ),
    (
        "negative_divisor",
        "example (x y : Int) (h : (-3 : Int) ∣ (2*x + y + 4)) : (-6 : Int) ∣ (4*x + 2*y + 8) := by\n  simp +arith only\n  guard_target =ₛ -3 ∣ (2*x + y + 4)\n  exact h\n\
         example (x : Int) (h : (1 : Int) ∣ 2) : (-3 : Int) ∣ (x-x-6) := by\n  simp +arith only\n  guard_target =ₛ @Dvd.dvd Int Int.instDvd 1 2\n  exact h\n",
    ),
    (
        "impossible_divisibility",
        "example (x : Int) (h : (6 : Int) ∣ (4*x + 3)) : False := by simp +arith only at h\n",
    ),
];

const REJECTED: &[(&str, &str)] = &[
    (
        "equation_no_progress",
        "example (x y : Int) : x = y := by simp +arith only\n",
    ),
    (
        "constant_equation_no_progress",
        "example (x : Int) : x = 3 := by simp +arith only\n",
    ),
    (
        "false_equality",
        "example (x : Int) : x + 1 = x + 2 := by simp +arith only\n",
    ),
    (
        "false_inequality",
        "example (x : Int) : x + 1 ≤ x := by simp +arith only\n",
    ),
    (
        "zero_divisor",
        "example (x : Int) : (0 : Int) ∣ x := by simp +arith only\n",
    ),
    (
        "nonlinear_equality",
        "example (x : Int) : x*x = x := by simp +arith only\n",
    ),
    (
        "custom_addition",
        "def asymmetricAdd : HAdd Int Int Int := ⟨fun a _ => a⟩\n\
         example (x y : Int) : @HAdd.hAdd Int Int Int asymmetricAdd x y = y := by simp +arith only\n",
    ),
    (
        "invalid_ascribed_atom",
        "example (x : Int) : (x : Bool) - (x : Bool) = (0 : Int) := by simp +arith only\n",
    ),
    (
        "wrong_tightening",
        "example (x : Int) (h : x + 1 ≤ 0) : 6*x + 4 ≤ 9 := by\n  simp +arith only\n  guard_target =ₛ x + 1 ≤ 0\n  exact h\n",
    ),
];

#[test]
fn simp_arith_normalizes_int_terms_constraints_and_divisibility_as_the_pin_does() {
    let Some(lib) = pinned_lib() else { return };
    let root = workspace();
    for (name, program) in ACCEPTED {
        let (code, stderr, pinned) = check_with_header(&lib, &root, name, HEADER, program);
        assert_eq!(
            pinned.unwrap_or(0),
            0,
            "{name}: the pinned lean rejects {program}"
        );
        assert_eq!(code, 0, "{name}: {program}\n{stderr}");
    }
    for (name, program) in REJECTED {
        let (code, stderr, pinned) = check_with_header(&lib, &root, name, HEADER, program);
        assert_ne!(
            pinned.unwrap_or(1),
            0,
            "{name}: the pinned lean accepts {program}"
        );
        assert_ne!(code, 0, "{name}: accepted {program}");
        assert!(
            !stderr.contains("unexpected syntax"),
            "{name}: unsupported rather than rejected\n{stderr}"
        );
    }
}
