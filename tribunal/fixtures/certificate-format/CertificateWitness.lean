/-
Pinned external-checker witness for scripts/e2e/certificate_format_no_mock_e2e.sh.
The Reference compiles it only inside the Tribunal; it is never product input.
-/
theorem certificate_witness_add_zero (n : Nat) : n + 0 = n := Nat.add_zero n
