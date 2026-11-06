//! `split` through the installed drop-in `lean`, over `prelude` and the smallest `Init` modules
//! that have it. The pin's `split` (vendored `Lean/Elab/Tactic/Split.lean`) splits the first `if`
//! of the goal, or of one hypothesis, by cases on its decision (`SplitIf.splitIfAt?`, vendored
//! `Lean/Meta/Tactic/SplitIf.lean:261-271`), tagging the cases `isTrue` and `isFalse` and naming
//! the hypothesis `h✝`, then reduces in each case every conditional a hypothesis decides
//! (`simpIfTarget`/`simpIfLocalDecl` under `backward.split`, lines 284-313). Exhaustive source
//! constructor matches use checked recursor splitters in their written alternative order.
//! Overlapping/matrix and unrecorded matchers retain a typed refusal.
//!
//! Every program was run through the pinned `lean` v4.32.0 with the same header first
//! (2026-10-23), and its output is compared with the pinned binary's again when that is present.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

/// Conditionals in the goal and in hypotheses: source `if`s on a proposition and on a `Bool`,
/// with and without evidence, nested, applied, under a binder, and the pin's `ite` written out;
/// `split at`, `split at *`, `split <;>`, `next` naming, and proofs closed after the split.
const PROGRAM: &str = r#"prelude
import Init.SimpLemmas
example (x : Nat) : (if x = 0 then 1 else 2) > 0 := by
  split
  trace_state
  all_goals sorry
example (x : Nat) (f : (x : Nat) → x ≠ 0 → Nat) : (if h : x ≠ 0 then f x h else 2) > 0 := by
  split
  trace_state
  all_goals sorry
example (x y : Nat) : (if x = 0 then (if y = 0 then 1 else 2) else 3) > 0 := by
  split
  split
  trace_state
  all_goals sorry
example (x y : Nat) (hy : y = 0) : (if x = 0 then (if y = 0 then 1 else 2) else 3) > 0 := by
  split
  trace_state
  all_goals sorry
example (x y : Nat) (h : (if x = y then 1 else 2) = 3) : False := by
  split at h
  trace_state
  all_goals sorry
example (p : Prop) [Decidable p] (h : ite p 1 2 = 3) (h2 : h = h) : True := by
  split at h
  trace_state
  all_goals sorry
example (b : Bool) (f g : Nat → Nat) : (if b then f else g) 3 = 37 := by
  split
  trace_state
  all_goals sorry
example (x : Nat) : ∀ y : Nat, (if x = 0 then y else 2) ≥ 0 := by
  split
  trace_state
  all_goals sorry
example (x y : Nat) : ite (x = 0) (ite (y = 0) 1 2) 3 > 0 := by
  split
  trace_state
  all_goals sorry
example (x : Nat) (h1 : True) (h : (if x = 0 then 1 else 2) = 5) : False := by
  split at *
  trace_state
  all_goals sorry
example (x : Nat) : (if x = 0 then 1 else 2) > 0 := by
  split
  next h =>
    trace_state
    decide
  next h => decide
example (b : Bool) : (if b then 1 else if b then 1 else 0) = (if b then 1 else 0) := by
  split <;> rfl
example (b : Bool) : (if _h : (if b then true else true) then 1 else 2) = 1 := by
  split
  next h' => rfl
  next h' => rfl
example (x : Nat) (f : (x : Nat) → x = 0 → Nat) (hf : ∀ x h, f x h = 0) :
    (if h : x = 0 then f x h else 0) = 0 := by
  split
  next h => exact hf x h
  next => rfl
example (x y : Nat) (h : (if x = y then 1 else 2) = 1) : x = y := by
  split at h
  next hxy => exact hxy
  next => exact Nat.noConfusion (Nat.succ.inj h)
example (p : Prop) [Decidable p] (a b : Nat) (h : (if p then a else b) = 3) (hb : b = 3) :
    (if p then a else b) = 3 := by
  split at h
  next hp =>
    split
    next => exact h
    next => contradiction
  next hp =>
    split
    next => contradiction
    next => exact hb
example {A B : Type} {p : Prop} [Decidable p] (h : if p then A else B) : Sum A B := by
  split at h
  next => exact .inl h
  next => exact .inr h
example (x : Nat) (h : ∀ y : Nat, (if x = 0 then y else 0) = y) : x = 0 := by
  split at h
  next hx => exact hx
  next => exact absurd (h 1) (fun h1 => Nat.noConfusion h1)
"#;

/// The pin's output for [`PROGRAM`]. A hypothesis decides every conditional it can, not only the
/// split one (`hy`); a dependent hypothesis stays, shadowed, beside its reduced copy.
const EXPECTED: &str = r#"case isTrue
x : Nat
h✝ : x = 0
⊢ 1 > 0

case isFalse
x : Nat
h✝ : ¬x = 0
⊢ 2 > 0
Split.lean:3:0: warning: declaration uses `sorry`
case isTrue
x : Nat
f : (x : Nat) → x ≠ 0 → Nat
h✝ : x ≠ 0
⊢ f x h✝ > 0

case isFalse
x : Nat
f : (x : Nat) → x ≠ 0 → Nat
h✝ : ¬x ≠ 0
⊢ 2 > 0
Split.lean:7:0: warning: declaration uses `sorry`
case isTrue.isTrue
x y : Nat
h✝¹ : x = 0
h✝ : y = 0
⊢ 1 > 0

case isTrue.isFalse
x y : Nat
h✝¹ : x = 0
h✝ : ¬y = 0
⊢ 2 > 0

case isFalse
x y : Nat
h✝ : ¬x = 0
⊢ 3 > 0
Split.lean:11:0: warning: declaration uses `sorry`
case isTrue
x y : Nat
hy : y = 0
h✝ : x = 0
⊢ 1 > 0

case isFalse
x y : Nat
hy : y = 0
h✝ : ¬x = 0
⊢ 3 > 0
Split.lean:16:0: warning: declaration uses `sorry`
case isTrue
x y : Nat
h✝ : x = y
h : 1 = 3
⊢ False

case isFalse
x y : Nat
h✝ : ¬x = y
h : 2 = 3
⊢ False
Split.lean:20:0: warning: declaration uses `sorry`
case isTrue
p : Prop
inst✝ : Decidable p
h✝¹ : ite p 1 2 = 3
h2 : h✝¹ = h✝¹
h✝ : p
h : 1 = 3
⊢ True

case isFalse
p : Prop
inst✝ : Decidable p
h✝¹ : ite p 1 2 = 3
h2 : h✝¹ = h✝¹
h✝ : ¬p
h : 2 = 3
⊢ True
Split.lean:24:0: warning: declaration uses `sorry`
case isTrue
b : Bool
f g : Nat → Nat
h✝ : b = true
⊢ f 3 = 37

case isFalse
b : Bool
f g : Nat → Nat
h✝ : ¬b = true
⊢ g 3 = 37
Split.lean:28:0: warning: declaration uses `sorry`
case isTrue
x : Nat
h✝ : x = 0
⊢ ∀ (y : Nat), y ≥ 0

case isFalse
x : Nat
h✝ : ¬x = 0
⊢ ∀ (y : Nat), 2 ≥ 0
Split.lean:32:0: warning: declaration uses `sorry`
case isTrue
x y : Nat
h✝ : x = 0
⊢ ite (y = 0) 1 2 > 0

case isFalse
x y : Nat
h✝ : ¬x = 0
⊢ 3 > 0
Split.lean:36:0: warning: declaration uses `sorry`
case isTrue
x : Nat
h1 : True
h✝ : x = 0
h : 1 = 5
⊢ False

case isFalse
x : Nat
h1 : True
h✝ : ¬x = 0
h : 2 = 5
⊢ False
Split.lean:40:0: warning: declaration uses `sorry`
x : Nat
h : x = 0
⊢ 1 > 0
"#;

/// An `ite` from an imported statement (`Nat.div_eq`), in the goal and in a hypothesis.
const IMPORTED: &str = r#"prelude
import Init.Data.Nat.Div.Basic
example (n : Nat) : (n + 2) / 2 < n + 3 := by
  rw [Nat.div_eq]
  split
  trace_state
  all_goals sorry
example (n : Nat) (h : n / 2 = 5) : 2 ≤ n := by
  rw [Nat.div_eq] at h
  split at h
  next hn => exact hn.2
  next => exact Nat.noConfusion h
"#;

/// The pin's output for [`IMPORTED`].
const IMPORTED_EXPECTED: &str = r#"case isTrue
n : Nat
h✝ : 0 < 2 ∧ 2 ≤ n + 2
⊢ (n + 2 - 2) / 2 + 1 < n + 3

case isFalse
n : Nat
h✝ : ¬(0 < 2 ∧ 2 ≤ n + 2)
⊢ 0 < n + 3
Imported.lean:3:0: warning: declaration uses `sorry`
"#;

/// Programs the pin refuses: the name, the program, the pin's message (before the goal it
/// appends), and this engine's refusal, which names the hypothesis where the pin prints its type.
const REFUSED: &[(&str, &str, &str, &str)] = &[
    (
        "Nothing.lean",
        "prelude\nimport Init.SimpLemmas\nexample (x : Nat) : x = x := by\n  split\n",
        "Tactic `split` failed: Could not split an `if` or `match` expression in the goal\n\nHint: Use `set_option trace.split.failure true` to display additional diagnostic information\n",
        "Tactic `split` failed: Could not split an `if` or `match` expression in the goal\n\nHint: Use `set_option trace.split.failure true` to display additional diagnostic information\n",
    ),
    (
        "Conj.lean",
        "prelude\nimport Init.SimpLemmas\nexample (p q : Prop) (h : p ∧ q) : p := by\n  split at h\n",
        "Tactic `split` failed: Could not split an `if` or `match` expression in the type `p ∧ q` of `h`\n\nHint: If you meant to destruct this conjunction, use the `cases` tactic instead\n\nHint: Use `set_option trace.split.failure true` to display additional diagnostic information\n",
        "Tactic `split` failed: Could not split an `if` or `match` expression in the type of `h`\n\nHint: If you meant to destruct this conjunction, use the `cases` tactic instead\n\nHint: Use `set_option trace.split.failure true` to display additional diagnostic information\n",
    ),
    (
        "Wild.lean",
        "prelude\nimport Init.SimpLemmas\nexample (x : Nat) (h1 : True) : x = x := by\n  split at *\n",
        "Tactic `split` failed: Could not split the goal or any of the following hypotheses: `h1`\n\nNote: `split at *` does not attempt to split at non-propositional hypotheses or those on which other hypotheses depend. It may still be possible to manually split a hypothesis using `split at`\n\nHint: Use `set_option trace.split.failure true` to display additional diagnostic information\n",
        "Tactic `split` failed: Could not split the goal or any of the following hypotheses: `h1`\n\nNote: `split at *` does not attempt to split at non-propositional hypotheses or those on which other hypotheses depend. It may still be possible to manually split a hypothesis using `split at`\n\nHint: Use `set_option trace.split.failure true` to display additional diagnostic information\n",
    ),
    (
        "Term.lean",
        "prelude\nimport Init.SimpLemmas\nexample (p : Prop) [Decidable p] (h : if p then True else True) : True := by\n  split h\n",
        "Tactic `split` failed: Specifying a term to split is not supported yet\n\nHint: To apply `split` at the hypothesis `h`, use `split at h`:\n  split a\u{332}t\u{332} \u{332}h\n",
        "Tactic `split` failed: Specifying a term to split is not supported yet\n\nHint: To apply `split` at the hypothesis `h`, use `split at h`:\n  split a\u{332}t\u{332} \u{332}h\n",
    ),
    (
        "Many.lean",
        "prelude\nimport Init.SimpLemmas\nexample (p q : Prop) (h : p) (h2 : q) : p := by\n  split at h h2\n",
        "Tactic `split` failed: Specifying multiple targets (hypotheses`h` and `h2`) is not supported\n\nHint: Specify a single target to split, or use `split at *` to split the first target that can be automatically split\n",
        "Tactic `split` failed: Specifying multiple targets (hypotheses`h` and `h2`) is not supported\n\nHint: Specify a single target to split, or use `split at *` to split the first target that can be automatically split\n",
    ),
];

/// A catch-all `match` whose second splitter branch needs an exclusion premise, rather than
/// a successor constructor. This remains outside the explicit-constructor implementation.
const MATCH: &str = "prelude\nimport Init.SimpLemmas\nexample (x : Nat) : (match x with | 0 => 1 | _ => 2) > 0 := by\n  split\n  all_goals sorry\n";

const CONSTRUCTOR_MATCHES: &str = r#"prelude
import Init.SimpLemmas
set_option linter.unusedVariables false
example (x : Nat) : (match x with | Nat.zero => 1 | Nat.succ y => y + 2) > 0 := by
  split
  trace_state
  all_goals sorry
example (b : Bool) : (match b with | true => 7 | false => 3) > 0 := by
  split
  trace_state
  all_goals sorry
example (x : Option Nat) : (match x with | .some y => y + 1 | .none => 3) > 0 := by
  split
  trace_state
  all_goals sorry
example (x : Nat) (h : (match x with | Nat.zero => 1 | Nat.succ y => y + 2) = 0) : False := by
  split at h
  trace_state
  all_goals sorry
"#;

const CONSTRUCTOR_MATCHES_EXPECTED: &str = r#"case h_1
x✝ : Nat
⊢ 1 > 0

case h_2
x✝ y✝ : Nat
⊢ y✝ + 2 > 0
ConstructorMatches.lean:4:0: warning: declaration uses `sorry`
case h_1
b✝ : Bool
⊢ 7 > 0

case h_2
b✝ : Bool
⊢ 3 > 0
ConstructorMatches.lean:8:0: warning: declaration uses `sorry`
case h_1
x✝ : Option Nat
y✝ : Nat
⊢ y✝ + 1 > 0

case h_2
x✝ : Option Nat
⊢ 3 > 0
ConstructorMatches.lean:12:0: warning: declaration uses `sorry`
case h_1
x✝ : Nat
h : 1 = 0
⊢ False

case h_2
x✝ y✝ : Nat
h : y✝ + 2 = 0
⊢ False
ConstructorMatches.lean:16:0: warning: declaration uses `sorry`
"#;

const CONSTRUCTOR_PROOFS: &str = r#"prelude
import Init.SimpLemmas
set_option linter.unusedVariables false
theorem split_nat_reconstruction (x : Nat) : (match x with | Nat.zero => 0 | Nat.succ n => n.succ) = x := by
  split <;> rfl
theorem split_function_valued_match (b : Bool) (f g : Nat → Nat) (x : Nat) :
    (match b with | true => f | false => g) x =
      (match b with | true => f x | false => g x) := by
  split <;> rfl
theorem split_option_some_first (x : Option Nat) (h : match x with | .some n => n = 0 | .none => False) :
    x = Option.some 0 := by
  split at h
  next n => cases h; rfl
  next => exact False.elim h
theorem split_option_none_first (x : Option Nat) (h : match x with | .none => False | .some n => n = 0) :
    x = Option.some 0 := by
  split at *
  next => exact False.elim h
  next n => cases h; rfl
theorem split_polymorphic_option {α : Type} (x : Option α) (p : α → Prop) (hp : ∀ a, p a) :
    match x with | .none => True | .some a => p a := by
  split
  next => exact True.intro
  next a => exact hp a
inductive Side where
  | right | left | center
theorem split_enumeration_source_order (s : Side) : match s with | .left => True | .center => True | .right => True := by
  split <;> exact True.intro
"#;

/// Computed discriminants are generalized only at their matcher applications. The ordinary
/// occurrences in branch bodies, the rest of the target and existing hypotheses stay fixed;
/// the generated equality is the evidence relating each constructor to the original term.
const COMPUTED_MATCH_PROOFS: &str = r#"prelude
import Init.SimpLemmas
set_option linter.unusedVariables false
theorem split_computed_reconstruction (f : Nat → Nat) (x : Nat) :
    (match f x with | Nat.zero => 0 | Nat.succ n => n.succ) = f x := by
  split
  next h => symm; exact h
  next n h => symm; exact h
theorem split_computed_branch_occurrences (f : Nat → Nat) (x : Nat) :
    (match f x with | Nat.zero => f x | Nat.succ n => f x) = f x := by
  split
  all_goals change f x = f x
  all_goals rfl
theorem split_computed_existing_hypothesis (f : Nat → Nat) (x : Nat)
    (p : Nat → Prop) (hp : p (f x)) :
    match f x with | Nat.zero => p (f x) | Nat.succ n => p (f x) := by
  split <;> exact hp
theorem split_computed_under_binder (f : Nat → Nat) (x : Nat) :
    ∀ y : Nat, (match f x with | Nat.zero => 0 | Nat.succ n => n.succ) = f x := by
  split
  next h => intro y; symm; exact h
  next n h => intro y; symm; exact h
theorem split_computed_hypothesis (f : Nat → Option Nat) (x : Nat)
    (h : match f x with | .some n => n = 0 | .none => False) : f x = Option.some 0 := by
  split at h
  next n heq => cases h; exact heq
  next heq => exact False.elim h
theorem split_computed_wildcard (f : Nat → Option Nat) (x : Nat)
    (h : match f x with | .none => False | .some n => n = 0) : f x = Option.some 0 := by
  split at *
  next heq => exact False.elim h
  next n heq => cases h; exact heq
theorem split_computed_let_argument (f : Nat → Nat) (x : Nat) : True := by
  let y := x
  have h : (match f y with | Nat.zero => 0 | Nat.succ n => n.succ) = f y := by
    split
    next h => symm; exact h
    next n h => symm; exact h
  exact True.intro
"#;

/// The last field distinguishes false/incomplete proofs that must reach branch obligations
/// from a direct let-bound discriminant, which the pin's splitter itself refuses.
const COMPUTED_MATCH_REFUSALS: &[(&str, &str, bool)] = &[
    (
        "ComputedFalseBranch.lean",
        "example (f : Nat → Bool) (x : Nat) : (match f x with | true => True | false => False) := by\n  split <;> exact True.intro\n",
        true,
    ),
    (
        "ComputedMissingBranch.lean",
        "example (f : Nat → Bool) (x : Nat) : (match f x with | true => True | false => True) := by\n  split\n  exact True.intro\n",
        true,
    ),
    (
        "ComputedWrongEquality.lean",
        "example (f : Nat → Nat) (x : Nat) : (match f x with | Nat.zero => 1 | Nat.succ n => n.succ) = f x := by\n  split\n  next h => symm; exact h\n  next n h => symm; exact h\n",
        true,
    ),
    (
        "DirectLetDiscriminant.lean",
        "example (f : Nat → Nat) (x : Nat) : True := by\n  let y := f x\n  have h : (match y with | Nat.zero => 0 | Nat.succ n => n.succ) = y := by\n    split <;> rfl\n  exact True.intro\n",
        false,
    ),
];

/// Source conditionals must have the same heads as the imported conditional lemmas.
/// A recursor with equivalent evaluation cannot replace `ite`/`dite` here: `simp only`
/// and `rw` select the imported lemmas by their actual applications.
const SOURCE_CONDITIONALS: &str = r#"prelude
import Init.SimpLemmas
import Init.ByCases
set_option linter.unusedVariables false
example : (if True then 1 else 2) = 1 := by simp only [ite_true]
example : (if True then 1 else 2) = 1 := by simp only [if_true]
example : (if False then 1 else 2) = 2 := by simp only [ite_false]
example (c : Prop) [Decidable c] (a : Nat) : (if c then a else a) = a := by
  simp only [ite_self]
example (c : Prop) [Decidable c] (a b : Nat) (h : c) : (if c then a else b) = a := by
  rw [if_pos h]
example (c : Prop) [Decidable c] (a b : Nat) (h : ¬ c) : (if c then a else b) = b := by
  rw [if_neg h]
example (c : Prop) [Decidable c] (yes : c → Nat) (no : ¬ c → Nat) (h : c) :
    (if h : c then yes h else no h) = yes h := by
  rw [dif_pos h]
example (c : Prop) [Decidable c] (yes : c → Nat) (no : ¬ c → Nat) (h : ¬ c) :
    (if h : c then yes h else no h) = no h := by
  rw [dif_neg h]
example (b : Bool) (a c : Nat) : (if b then a else c) = ite (b = true) a c := rfl
example (b : Bool) (h : b = true) (f : b = true → Nat) :
    (if h : b then f h else 0) = f h := by
  rw [dif_pos h]
example (c : Prop) [Decidable c] (a : Nat) :
    (if _ : c then a else a) = a := by
  split <;> rfl
example (c : Prop) [Decidable c] (a b : Nat) :
    (if c then a else b) = (if c then a else b) := by
  split <;> rfl
def inferred (b : Bool) := if b then 17 else 19
example : inferred true = 17 := rfl
example : inferred false = 19 := rfl
def shadow (h : Nat) (b : Bool) :=
  let result := if h : b then (fun h : Nat => h + 1) 40 else 7
  h + result
example : shadow 1 true = 42 := rfl
example : shadow 1 false = 8 := rfl
example (p q : Prop) [Decidable p] [Decidable q]
    (yes : p → q → Nat) (no : Nat) (hp : p) (hq : q) :
    (if h : p then (if h : q then yes hp h else no) else no) = yes hp hq := by
  rw [dif_pos hp, dif_pos hq]
"#;

/// Printing uses exactly the notation imported by this header. `Init.SimpLemmas`
/// has no `ite` unexpander: the pin prints `ite`, while `dite` has binder syntax.
const SOURCE_CONDITIONAL_PRINTING: &str = r#"prelude
import Init.SimpLemmas
set_option linter.unusedVariables false
def choose (c : Prop) [Decidable c] (a b : Nat) : Nat := if c then a else b
#print choose
#check if 1 = 1 then 3 else 4
#check fun (b : Bool) => if b then 1 else 2
def chooseEvidence (c : Prop) [Decidable c] (yes : c → Nat) (no : ¬ c → Nat) : Nat :=
  if h : c then yes h else no h
#print chooseEvidence
#check fun (c : Prop) [Decidable c] => if c then Nat.succ else Nat.pred
#check if _ : True then 1 else 0
def globalName : Nat := 9
def shadowGlobal (p : Prop) [Decidable p] : Nat :=
  dite p (fun globalName => 0) (fun other => globalName)
#print shadowGlobal
"#;

const SOURCE_CONDITIONAL_PRINTED: &str = "def choose : (c : Prop) → [Decidable c] → Nat → Nat → Nat :=\n\
fun c [Decidable c] a b => ite c a b\n\
ite (1 = 1) 3 4 : Nat\n\
fun b => ite (b = true) 1 2 : Bool → Nat\n\
def chooseEvidence : (c : Prop) → [Decidable c] → (c → Nat) → (¬c → Nat) → Nat :=\n\
fun c [Decidable c] yes no => if h : c then yes h else no h\n\
fun c [Decidable c] => ite c Nat.succ Nat.pred : (c : Prop) → [Decidable c] → Nat → Nat\n\
if x : True then 1 else 0 : Nat\n\
def shadowGlobal : (p : Prop) → [Decidable p] → Nat :=\n\
fun p [Decidable p] => if globalName : p then 0 else _root_.globalName\n";

const SOURCE_CONDITIONAL_NOTATION: &str = "def choose : (c : Prop) → [Decidable c] → Nat → Nat → Nat :=\n\
fun c [Decidable c] a b => if c then a else b\n\
if 1 = 1 then 3 else 4 : Nat\n\
fun b => if b = true then 1 else 2 : Bool → Nat\n\
def chooseEvidence : (c : Prop) → [Decidable c] → (c → Nat) → (¬c → Nat) → Nat :=\n\
fun c [Decidable c] yes no => if h : c then yes h else no h\n\
fun c [Decidable c] => if c then Nat.succ else Nat.pred : (c : Prop) → [Decidable c] → Nat → Nat\n\
if x : True then 1 else 0 : Nat\n\
def shadowGlobal : (p : Prop) → [Decidable p] → Nat :=\n\
fun p [Decidable p] => if globalName : p then 0 else _root_.globalName\n";

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
        .filter(|lib| lib.join("Init/Data/Nat/Div/Basic.olean").is_file());
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
        "fln-split-tactic-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

/// The pinned `lean`'s stdout and exit code on `name` in `root`, when the binary is present.
/// Both binaries run from `root` on a relative name, so a message names the file as given.
fn pinned(lib: &Path, root: &Path, name: &str) -> Option<(i32, String)> {
    let lean = lib.parent()?.parent()?.join("bin/lean");
    if !lean.is_file() {
        return None;
    }
    let output = Command::new(lean)
        .arg(name)
        .current_dir(root)
        .env("LEAN_PATH", lib)
        .output()
        .expect("run the pinned lean");
    Some((
        output.status.code().expect("normal pinned exit"),
        String::from_utf8(output.stdout).unwrap(),
    ))
}

/// The installed `lean` on `name` in `root`: its exit code, stdout and stderr. Every program of
/// a test shares one import record, so only the first admits its imports cold.
fn ours(lib: &Path, root: &Path, name: &str) -> (i32, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(name)
        .current_dir(root)
        .env("LEAN_PATH", lib)
        .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
        .output()
        .expect("run lean");
    (
        output.status.code().expect("normal exit"),
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

/// `program` as `name` in `root`, its output compared with `expected`, the pin's.
fn accepted(lib: &Path, root: &Path, name: &str, program: &str, expected: &str) {
    std::fs::write(root.join(name), program).unwrap();
    if let Some((code, stdout)) = pinned(lib, root, name) {
        assert_eq!((code, stdout.as_str()), (0, expected), "the pin moved");
    }
    let (code, stdout, stderr) = ours(lib, root, name);
    assert_eq!(code, 0, "{stderr}");
    assert_eq!(stdout, expected, "{stderr}");
}

#[test]
fn split_cases_on_conditionals_as_the_pin_does() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    accepted(&lib, &root, "Split.lean", PROGRAM, EXPECTED);
}

#[test]
fn split_cases_on_an_imported_ite_as_the_pin_does() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    accepted(&lib, &root, "Imported.lean", IMPORTED, IMPORTED_EXPECTED);
}

#[test]
fn split_constructor_matches_preserves_source_order_and_goal_contexts() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    accepted(
        &lib,
        &root,
        "ConstructorMatches.lean",
        CONSTRUCTOR_MATCHES,
        CONSTRUCTOR_MATCHES_EXPECTED,
    );
    accepted(
        &lib,
        &root,
        "ConstructorProofs.lean",
        CONSTRUCTOR_PROOFS,
        "",
    );
}

/// The same complete proofs also run over the native admitted seed, independently of the
/// installed library and its import cache. Both failing programs must reach real split goals.
#[test]
fn split_constructor_matches_checks_native_seed_proofs_and_every_branch() {
    let limits = fln::SourceCheckLimits::new(fln::EngineAdmissionLimits::new(
        fln::Budget::for_stack_bytes(8 * 1024 * 1024),
    ));
    let options = fln::KVMap::new();
    let base = fln::Engine::with_source_seed(limits.admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = base.logical_root(&options);
    let program = CONSTRUCTOR_PROOFS
        .strip_prefix("prelude\nimport Init.SimpLemmas\nset_option linter.unusedVariables false\n")
        .expect("the shared proof fixture has only its import header removed");
    let checked = base
        .check_source_files(&[program.as_bytes()], &options, limits)
        .unwrap_or_else(|error| panic!("{program}\n{error:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(checked.theorems, 6, "every theorem checks an actual proof");
    assert_eq!(base.logical_root(&options), root);

    for program in [
        "example (b : Bool) : (match b with | true => True | false => False) := by\n  split <;> exact True.intro\n",
        "example (b : Bool) : (match b with | true => True | false => True) := by\n  split\n  exact True.intro\n",
    ] {
        let error = base
            .check_source_files(&[program.as_bytes()], &options, limits)
            .expect_err("a false or unfinished split branch must reject the theorem");
        assert!(
            !format!("{error:?}").contains("SplitMatchUnsupported"),
            "the negative control must split the match: {error:?}"
        );
        assert_eq!(base.logical_root(&options), root);
    }
}

#[test]
fn split_computed_discriminants_checks_native_proofs_and_every_branch() {
    let limits = fln::SourceCheckLimits::new(fln::EngineAdmissionLimits::new(
        fln::Budget::for_stack_bytes(8 * 1024 * 1024),
    ));
    let options = fln::KVMap::new();
    let base = fln::Engine::with_source_seed(limits.admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = base.logical_root(&options);
    let program = COMPUTED_MATCH_PROOFS
        .strip_prefix("prelude\nimport Init.SimpLemmas\nset_option linter.unusedVariables false\n")
        .expect("only the shared fixture's import header is removed");
    let checked = base
        .check_source_files(&[program.as_bytes()], &options, limits)
        .unwrap_or_else(|error| panic!("{program}\n{error:?}"))
        .into_complete()
        .unwrap();
    assert_eq!(checked.theorems, 7, "every branch supplies a checked proof");
    assert_eq!(base.logical_root(&options), root);
    for (name, program, must_split) in COMPUTED_MATCH_REFUSALS {
        let error = base
            .check_source_files(&[program.as_bytes()], &options, limits)
            .expect_err("false or unfinished computed branches must reject the theorem");
        if *must_split {
            assert!(
                !format!("{error:?}").contains("SplitMatchUnsupported"),
                "{name} must reach the generated proof obligations: {error:?}"
            );
        }
        assert_eq!(base.logical_root(&options), root);
    }
}

#[test]
fn split_computed_discriminants_matches_the_pin() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    accepted(
        &lib,
        &root,
        "ComputedMatches.lean",
        COMPUTED_MATCH_PROOFS,
        "",
    );
    for (name, body, must_split) in COMPUTED_MATCH_REFUSALS {
        let program = format!("prelude\nimport Init.SimpLemmas\n{body}");
        std::fs::write(root.join(name), program).unwrap();
        if let Some((code, stdout)) = pinned(&lib, &root, name) {
            assert_eq!(code, 1, "{name}: the pin moved: {stdout}");
        }
        let (code, stdout, stderr) = ours(&lib, &root, name);
        assert_eq!(code, 1, "{name}: {stdout}{stderr}");
        if *must_split {
            assert!(
                !stderr.contains("split on a `match` expression is not implemented"),
                "{stderr}"
            );
        }
    }
}

#[test]
fn split_constructor_matches_keeps_every_branch_as_a_checked_obligation() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    for (name, body) in [
        (
            "FalseBranch.lean",
            "example (b : Bool) : (match b with | true => True | false => False) := by\n  split <;> exact True.intro\n",
        ),
        (
            "MissingBranch.lean",
            "example (b : Bool) : (match b with | true => True | false => True) := by\n  split\n  exact True.intro\n",
        ),
    ] {
        let program = format!("prelude\nimport Init.SimpLemmas\n{body}");
        std::fs::write(root.join(name), program).unwrap();
        if let Some((code, stdout)) = pinned(&lib, &root, name) {
            assert_eq!(code, 1, "{name}: the pin moved: {stdout}");
        }
        let (code, stdout, stderr) = ours(&lib, &root, name);
        assert_eq!(code, 1, "{name}: {stdout}{stderr}");
        assert!(
            !stderr.contains("split on a `match` expression is not implemented"),
            "{stderr}"
        );
    }
}

#[test]
fn source_conditionals_use_imported_ite_and_dite_lemmas() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    accepted(&lib, &root, "SourceIf.lean", SOURCE_CONDITIONALS, "");
}

#[test]
fn source_conditionals_print_with_the_imported_notation() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    accepted(
        &lib,
        &root,
        "PrintIf.lean",
        SOURCE_CONDITIONAL_PRINTING,
        SOURCE_CONDITIONAL_PRINTED,
    );
    let with_notation = SOURCE_CONDITIONAL_PRINTING.replacen(
        "import Init.SimpLemmas",
        "import Init.SimpLemmas\nimport Init.NotationExtra",
        1,
    );
    accepted(
        &lib,
        &root,
        "PrintIfNotation.lean",
        &with_notation,
        SOURCE_CONDITIONAL_NOTATION,
    );
}

#[test]
fn source_conditionals_do_not_refine_the_discriminant_or_leak_evidence() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    for (name, body) in [
        (
            "NoRefinement.lean",
            "example (b : Bool) : b = true ∨ b = false :=\n  if b then Or.inl rfl else Or.inr rfl\n",
        ),
        (
            "NoEvidenceLeak.lean",
            "def bad (b : Bool) : Nat :=\n  let n := if h : b then 1 else 2\n  h + n\n",
        ),
        (
            "BothBranchesChecked.lean",
            "def bad : Nat := if True then 1 else \"not a Nat\"\n",
        ),
    ] {
        let program = format!("prelude\nimport Init.SimpLemmas\n{body}");
        std::fs::write(root.join(name), program).unwrap();
        if let Some((code, stdout)) = pinned(&lib, &root, name) {
            assert_eq!(code, 1, "{name}: the pin moved: {stdout}");
        }
        let (code, stdout, stderr) = ours(&lib, &root, name);
        assert_eq!(code, 1, "{name}: {stdout}{stderr}");
        assert!(stdout.is_empty(), "{name}: {stdout}");
    }
}

#[test]
fn split_is_refused_where_the_pin_refuses_it() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    for (name, program, pin_message, message) in REFUSED {
        std::fs::write(root.join(name), program).unwrap();
        if let Some((code, stdout)) = pinned(&lib, &root, name) {
            assert_eq!(code, 1, "{name}: the pin moved: {stdout}");
            // The message, then the goal the pin appends after a blank line, if any.
            let at = stdout
                .find(&format!("error: {pin_message}"))
                .map(|at| at + "error: ".len() + pin_message.len());
            assert!(
                at.is_some_and(|at| stdout[at..].is_empty() || stdout[at..].starts_with('\n')),
                "{name}: the pin moved: {stdout}"
            );
        }
        let (code, stdout, stderr) = ours(&lib, &root, name);
        assert_eq!(code, 1, "{name}: {stdout}{stderr}");
        assert!(
            stderr.ends_with(&format!("refused source: {message}")),
            "{name}: {stderr}"
        );
    }
}

/// A catch-all needs the matcher's overlap/exclusion evidence. Constructor splitting must not
/// silently replace that goal by a narrower successor-constructor goal.
#[test]
fn split_on_a_match_is_refused_typed() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    std::fs::write(root.join("Match.lean"), MATCH).unwrap();
    if let Some((code, stdout)) = pinned(&lib, &root, "Match.lean") {
        assert_eq!(
            (code, stdout.as_str()),
            (0, "Match.lean:3:0: warning: declaration uses `sorry`\n"),
            "the pin moved"
        );
    }
    let (code, stdout, stderr) = ours(&lib, &root, "Match.lean");
    assert_eq!(code, 1, "{stdout}{stderr}");
    assert!(
        stderr.contains("split on a `match` expression is not implemented"),
        "{stderr}"
    );
}
