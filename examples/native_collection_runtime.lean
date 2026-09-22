-- Native collection execution: fln run --json examples/native_collection_runtime.lean
def words : List String := ["ab", "cde"]
def lengths : List Nat := List.map (fun s => String.length s) words
def answer : Nat := List.foldl (fun (acc n : Nat) => acc + n) 37 lengths
-- Structural collection proofs still go through the kernel; String.length is
-- evaluated by the native runtime rather than used as a reduction axiom.
theorem checked : List.length lengths = 2 := by rfl
#eval answer