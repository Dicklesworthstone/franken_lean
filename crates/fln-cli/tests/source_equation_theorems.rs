//! Equation theorems `f.eq_<n>`, `f.eq_def` and `f.eq_unfold`, generated when a command names
//! them, and `rw [f]` through them (the pin's `Lean.Meta.Eqns` reserved-name action and
//! `withRWRulesSeq`, vendored `Lean/Meta/Eqns.lean`, `Lean/Elab/Tactic/Rewrite.lean`).
//!
//! Through the installed `lean` over `prelude` with `Init.Core` (definitions by pattern matching
//! over `Init.Data.List.Basic`). Every program was run through the pinned `lean` v4.32.0 first
//! (2026-10-24): the expected output below is the pin's stdout, and each program is compared
//! with the pinned binary again when it is present. A program the pin accepts and this engine
//! does not generate the equations for is refused with the capability exit, never accepted
//! with other statements.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::Command;

const HEADER: &str = "prelude\nimport Init.Core\n";
/// The header of the definitions by pattern matching: list literals and `Nat` equality lemmas.
const MATCHED_HEADER: &str = "prelude\nimport Init.Data.List.Basic\n";

/// Programs the pin accepts, and its stdout.
const ACCEPTED: &[(&str, &str, &str)] = &[
    (
        "nonrecursive_statements",
        "def dist (n m : Nat) := n - m + (m - n)
#check @dist.eq_1
#check @dist.eq_def
#check @dist.eq_unfold
#check dist.eq_1
def answer := 42
#check @answer.eq_1
#check @answer.eq_def
#check @answer.eq_unfold
def withLet (n : Nat) : Nat := let k := n + 1; k * k
#check @withLet.eq_1
#check @withLet.eq_def
#check @withLet.eq_unfold
def poly {α : Type} (x : α) (xs : List α) : List α := x :: xs
#check @poly.eq_1
#check @poly.eq_def
#check @poly.eq_unfold
def poly2 (x : α) (xs : List α) : List α := x :: xs
#check @poly2.eq_1
#check poly2.eq_unfold
",
        "dist.eq_1 : ∀ (n m : Nat), dist n m = n - m + (m - n)
dist.eq_def : ∀ (n m : Nat), dist n m = n - m + (m - n)
dist.eq_unfold : dist = fun n m => n - m + (m - n)
dist.eq_1 (n m : Nat) : dist n m = n - m + (m - n)
answer.eq_1 : answer = 42
answer.eq_def : answer = 42
answer.eq_unfold : answer = 42
withLet.eq_1 : ∀ (n : Nat), withLet n = (n + 1) * (n + 1)
withLet.eq_def : ∀ (n : Nat),
  withLet n =
    have k := n + 1;
    k * k
withLet.eq_unfold : withLet = fun n =>
  have k := n + 1;
  k * k
@poly.eq_1 : ∀ {α : Type} (x : α) (xs : List α), poly x xs = x :: xs
@poly.eq_def : ∀ {α : Type} (x : α) (xs : List α), poly x xs = x :: xs
poly.eq_unfold : @poly = fun {α} x xs => x :: xs
@poly2.eq_1 : ∀ {α : Type u_1} (x : α) (xs : List α), poly2 x xs = x :: xs
poly2.eq_unfold.{u_1} : @poly2 = fun {α} x xs => x :: xs
",
    ),
    (
        "terms_and_rewrites",
        "def dist (n m : Nat) := n - m + (m - n)
def answer := 42
def withLet (n : Nat) : Nat := let k := n + 1; k * k
theorem t1 (n m : Nat) : dist n m = n - m + (m - n) := dist.eq_1 n m
theorem t2 (n m : Nat) : dist n m = n - m + (m - n) := by rw [dist]
theorem t3 (n : Nat) : withLet n = (n + 1) * (n + 1) := by rw [withLet]
theorem t4 : answer + 0 = 42 := by rw [answer]
theorem t5 (n m : Nat) : dist n m = n - m + (m - n) := by rw [dist.eq_def]
theorem t6 (n m : Nat) : dist n m = n - m + (m - n) := by rw [dist.eq_unfold]
example : dist 3 5 = 2 := by rw [dist]
namespace Foo
def twice (n : Nat) : Nat := n + n
theorem t7 (n : Nat) : twice n = n + n := twice.eq_1 n
end Foo
#check @Foo.twice.eq_1
",
        "Foo.twice.eq_1 : ∀ (n : Nat), Foo.twice n = n + n\n",
    ),
    (
        "locations_scopes_and_privacy",
        "def wrap (n : Nat) : Nat := n + 1
theorem h1 (n : Nat) (h : wrap n = 5) : n + 1 = 5 := by rw [wrap] at h; exact h
theorem h2 (n : Nat) : wrap (wrap n) = n + 1 + 1 := by rw [wrap, wrap]
theorem h3 (n : Nat) : n + 1 = wrap n := by rw [← wrap]
private def pw (n : Nat) : Nat := n * 2
theorem h4 (n : Nat) : pw n = n * 2 := pw.eq_1 n
#check @pw.eq_1
namespace A
def g (n : Nat) := n + 3
end A
open A in
theorem h5 : g 1 = 1 + 3 := g.eq_1 1
theorem h6 : A.g 1 = 1 + 3 := by rw [A.g]
",
        "pw.eq_1 : ∀ (n : Nat), pw n = n * 2\n",
    ),
    (
        "operands_ending_in_fun_or_have",
        "#check ∀ n : Nat, n = (have k := n + 1; k * k)
#check fun n : Nat => n = (have k := n + 1; k * k)
#check (id = fun x : Nat => x)
#check ((fun x : Nat => x) = id)
#check (id = fun x : Nat => x) ∧ True
",
        "∀ (n : Nat),
  n =
    have k := n + 1;
    k * k : Prop
fun n =>
  n =
    have k := n + 1;
    k * k : Nat → Prop
id = fun x => x : Prop
(fun x => x) = id : Prop
(id = fun x => x) ∧ True : Prop
",
    ),
];

/// Programs the pin refuses, and a line of this engine's refusal.
const REFUSED: &[(&str, &str, &str)] = &[
    (
        "beyond_the_equations",
        "def dist (n m : Nat) := n - m + (m - n)\n#check dist.eq_2\n",
        "Unknown identifier `dist.eq_2`",
    ),
    (
        "wrong_statement",
        "def dist (n m : Nat) := n - m + (m - n)\ntheorem bad (n m : Nat) : dist n m = n + m := dist.eq_1 n m\n",
        "",
    ),
    (
        "rewrite_then_false",
        "def answer := 42\ntheorem bad : answer = 41 := by rw [answer]\n",
        "",
    ),
    (
        "no_equation_rewrites",
        "def answer := 42\ntheorem y (n : Nat) : n = n + 0 := by rw [answer]\n",
        "Failed to rewrite using equation theorems for `answer`",
    ),
];

/// Definitions by pattern matching the pin accepts, and its stdout: the statements split the
/// alternatives as `Lean.Elab.Eqns.mkEqnTypes` does, with the overlap hypotheses of
/// `Lean.Meta.Match.MatchEqs` and the names `Lean.Meta.Split`'s `unifyEqs` leaves.
const MATCHED: &[(&str, &str, &str)] = &[
    (
        "literal_and_wildcard_alternatives",
        "def isZero : Nat → Bool | 0 => true | _ => false
#check @isZero.eq_1
#check @isZero.eq_2
#check isZero.eq_2
def bool2 : Bool → Bool → Bool
  | true, true => true
  | _, _ => false
#check bool2.eq_2
#check @bool2.eq_2
",
        "isZero.eq_1 : isZero 0 = true
isZero.eq_2 : ∀ (x : Nat), (x = 0 → False) → isZero x = false
isZero.eq_2 (x✝ : Nat) (x_2 : x✝ = 0 → False) : isZero x✝ = false
bool2.eq_2 (x✝ x✝¹ : Bool) (x_4 : x✝ = true → x✝¹ = true → False) : bool2 x✝ x✝¹ = false
bool2.eq_2 : ∀ (x x_1 : Bool), (x = true → x_1 = true → False) → bool2 x x_1 = false
",
    ),
    (
        "structural_recursion",
        "def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)
#check fib.eq_1
#check fib.eq_2
#check fib.eq_3
theorem a (n : Nat) : fib (n+2) = fib n + fib (n+1) := fib.eq_3 n
theorem b (n : Nat) : fib (Nat.succ (Nat.succ n)) = fib n + fib (n+1) := by rw [fib]
theorem c : fib 0 + fib 1 = 1 := by rw [fib, fib]
def add : Nat → Nat → Nat
  | n, 0 => n
  | n, m+1 => (add n m) + 1
#check @add.eq_1
#check add.eq_2
def pr : Nat → Nat → Nat
  | 0, _ => 0
  | k+1, m => pr k m + m
#check pr.eq_1
#check pr.eq_2
",
        "fib.eq_1 : fib 0 = 0
fib.eq_2 : fib 1 = 1
fib.eq_3 (n : Nat) : fib n.succ.succ = fib n + fib (n + 1)
add.eq_1 : ∀ (x : Nat), add x 0 = x
add.eq_2 (x✝ m : Nat) : add x✝ m.succ = add x✝ m + 1
pr.eq_1 (x✝ : Nat) : pr 0 x✝ = 0
pr.eq_2 (x✝ k : Nat) : pr k.succ x✝ = pr k x✝ + x✝
",
    ),
    (
        "overlapping_columns",
        "def g (x y : Nat) : Nat :=
  match x, y with
  | 0,   0 => 1
  | 0,   y => y
  | x+1, 5 => 2 * g x 0
  | x+1, y => 2 * g x y
#check g.eq_1
#check g.eq_2
#check g.eq_3
#check g.eq_4
def baz : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 1
  | n+1, m+1 => baz n m
#check @baz.eq_2
#check baz.eq_2
",
        "g.eq_1 : g 0 0 = 1
g.eq_2 (y : Nat) (x_2 : y = 0 → False) : g 0 y = y
g.eq_3 (x_2 : Nat) : g x_2.succ 5 = 2 * g x_2 0
g.eq_4 (y x_2 : Nat) (x_3 : y = 5 → False) : g x_2.succ y = 2 * g x_2 y
baz.eq_2 : ∀ (x : Nat), (x = 0 → False) → baz x 0 = 1
baz.eq_2 (x✝ : Nat) (x_3 : x✝ = 0 → False) : baz x✝ 0 = 1
",
    ),
    (
        "lists_and_named_patterns",
        "def lst2 : List Nat → Nat
  | a :: b :: rest => a + b + lst2 rest
  | _ => 0
#check @lst2.eq_1
#check lst2.eq_2
def len : List α → Nat
  | [] => 0
  | _ :: xs => len xs + 1
#check @len.eq_1
#check len.eq_2
def iota : Nat → List Nat
  | 0       => []
  | m@(n+1) => m :: iota n
#check iota.eq_1
#check iota.eq_2
@[simp] def f : List Nat → List Nat × List Nat
 | xs@(x :: ys@(y :: [])) => (xs, ys)
 | xs@(x :: ys@(y :: zs)) => f zs
 | _ => ([], [])
#check f.eq_1
#check f.eq_2
#check f.eq_3
",
        "lst2.eq_1 : ∀ (a b : Nat) (rest : List Nat), lst2 (a :: b :: rest) = a + b + lst2 rest
lst2.eq_2 (x✝ : List Nat) (x_2 : ∀ (a b : Nat) (rest : List Nat), x✝ = a :: b :: rest → False) : lst2 x✝ = 0
@len.eq_1 : ∀ {α : Type u_1}, len List.nil = 0
len.eq_2.{u_1} {α : Type u_1} (head : α) (xs : List α) : len (head :: xs) = len xs + 1
iota.eq_1 : iota 0 = List.nil
iota.eq_2 (n : Nat) : iota n.succ = n.succ :: iota n
lists_and_named_patterns.lean:19:7: warning: Variable name `x` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
lists_and_named_patterns.lean:19:16: warning: Variable name `y` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
lists_and_named_patterns.lean:20:3: warning: Variable name `xs` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
lists_and_named_patterns.lean:20:7: warning: Variable name `x` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
lists_and_named_patterns.lean:20:12: warning: Variable name `ys` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
lists_and_named_patterns.lean:20:16: warning: Variable name `y` is not explicitly referenced.

The binding can be removed (if unused) or named `_` (if used implicitly).

Note: This linter can be disabled with `set_option linter.unusedVariables false`
f.eq_1 (x_1 y : Nat) : f (x_1 :: y :: List.nil) = { fst := x_1 :: y :: List.nil, snd := y :: List.nil }
f.eq_2 (x_1 y : Nat) (zs : List Nat) (x_2 : zs = List.nil → False) : f (x_1 :: y :: zs) = f zs
f.eq_3 (x✝ : List Nat) (x_2 : ∀ (x y : Nat), x✝ = x :: y :: List.nil → False)
  (x_3 : ∀ (x y : Nat) (zs : List Nat), x✝ = x :: y :: zs → False) : f x✝ = { fst := List.nil, snd := List.nil }
",
    ),
    (
        "written_match_and_shared_matchers",
        "def pred' : Nat → Nat
  | 0 => 0
  | n+1 => n
def pred2 (n : Nat) : Nat := match n with
  | 0 => 0
  | k+1 => k
#check @pred2.eq_2
def foo (n : Nat) : Nat := match n with
  | 0 => 0
  | n+1 => n
#check @foo.eq_2
def len2 (xs : List α) : Nat := match xs with
  | [] => 0
  | _ :: ys => len2 ys + 1
#check len2.eq_2
def k : Nat → Nat := fun n => match n with
  | 0 => 1
  | _ => 2
#check k.eq_1
#check @k.eq_2
",
        "pred2.eq_2 : ∀ (n_1 : Nat), pred2 n_1.succ = n_1
foo.eq_2 : ∀ (n_1 : Nat), foo n_1.succ = n_1
len2.eq_2.{u_1} {α : Type u_1} (head : α) (ys : List α) : len2 (head :: ys) = len2 ys + 1
k.eq_1 : k 0 = 1
k.eq_2 : ∀ (n : Nat), (n = 0 → False) → k n = 2
",
    ),
    (
        "constructors_structures_instances",
        "def opt2 : Option (Option Nat) → Nat
  | some (some n) => n
  | some none => 1
  | none => 0
#check opt2.eq_1
#check opt2.eq_3
inductive T where
  | leaf
  | node (l r : T)
def size : T → Nat
  | .leaf => 1
  | .node l r => size l + size r
#check @size.eq_2
structure P where
  a : Nat
  b : Nat
def sw : P → P
  | ⟨x, y⟩ => ⟨y, x⟩
#check sw.eq_1
def sumL [Add α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x + sumL xs
#check @sumL.eq_2
#check sumL.eq_2
def get? {α : Type u} : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: as, n+1 => get? as n
#check get?.eq_3
namespace Foo
def dbl : Nat → Nat
  | 0 => 0
  | n+1 => dbl n + 2
end Foo
open Foo in
#check dbl.eq_2
",
        "opt2.eq_1 (n : Nat) : opt2 (some (some n)) = n
opt2.eq_3 : opt2 none = 0
size.eq_2 : ∀ (l r : T), size (l.node r) = size l + size r
sw.eq_1 (x_1 y : Nat) : sw { a := x_1, b := y } = { a := y, b := x_1 }
@sumL.eq_2 : ∀ {α : Type u_1} [inst : Add α] [inst_1 : OfNat α 0] (x_1 : α) (xs : List α),
  sumL (x_1 :: xs) = x_1 + sumL xs
sumL.eq_2.{u_1} {α : Type u_1} [Add α] [OfNat α 0] (x_1 : α) (xs : List α) : sumL (x_1 :: xs) = x_1 + sumL xs
get?.eq_3.{u} {α : Type u} (head : α) (as : List α) (n : Nat) : get? (head :: as) n.succ = get? as n
Foo.dbl.eq_2 (n : Nat) : dbl n.succ = dbl n + 2
",
    ),
    (
        "section_variables",
        "section
variable (k : Nat)
def addk : Nat → Nat
  | 0 => k
  | n+1 => addk n + 1
#check addk.eq_1
#check @addk.eq_2
theorem t1 (n : Nat) : addk k (n + 1) = addk k n + 1 := addk.eq_2 k n
theorem t2 (n : Nat) : addk k (n + 1) = addk k n + 1 := by rw [addk]
end
section
variable {α : Type} (d : α)
def headD : List α → α
  | [] => d
  | a :: _ => a
#check @headD.eq_1
#check headD.eq_2
end
namespace N
section
variable (k m : Nat)
def rec2 : Nat → Nat
  | 0 => k + m
  | n+1 => N.rec2 n
#check rec2.eq_2
end
end N
",
        "addk.eq_1 (k : Nat) : addk k 0 = k
addk.eq_2 : ∀ (k n : Nat), addk k n.succ = addk k n + 1
@headD.eq_1 : ∀ {α : Type} (d : α), headD d List.nil = d
headD.eq_2 {α : Type} (d a : α) (tail : List α) : headD d (a :: tail) = a
N.rec2.eq_2 (k m n : Nat) : rec2 k m n.succ = rec2 k m n
",
    ),
];

/// Programs the pin accepts whose equations this engine does not generate yet: each is
/// refused with the capability exit, naming the theorem.
const NOT_GENERATED: &[(&str, &str, &str)] = &[
    (
        "unfolding_a_definition_by_matching",
        "def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)
#check @fib.eq_def
",
        "the equation theorem `fib.eq_def` of `fib` is not generated here: the statement \
         contains a `match`",
    ),
    (
        "unfolding_constant_of_a_definition_by_matching",
        "def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib n + fib (n+1)
#check @fib.eq_unfold
",
        "the equation theorem `fib.eq_unfold` of `fib` is not generated here: the statement \
         contains a `match`",
    ),
    (
        "a_match_in_an_alternative",
        "def nested : Nat → Nat → Nat
  | 0, m => match m with | 0 => 0 | m => m
  | n+1, m => nested n m
#check nested.eq_1
",
        "the equation theorem `nested.eq_1` of `nested` is not generated here: the statement \
         contains a `match`",
    ),
    (
        "an_indexed_family",
        "inductive V : Nat → Type where
  | nil : V 0
  | cons : Nat → V n → V (n+1)
def hd : V (n+1) → Nat
  | .cons a _ => a
#check hd.eq_1
",
        "the equation theorem `hd.eq_1` of `hd` is not generated here: its `match` is not one \
         whose alternatives this engine records",
    ),
    (
        "well_founded_recursion",
        "import Init.Data.Nat.Div.Basic
def half : Nat → Nat
  | 0 => 0
  | n+1 => half (n / 2) + 1
termination_by n => n
decreasing_by exact Nat.lt_succ_of_le (Nat.div_le_self n 2)
#check half.eq_1
",
        "the equation theorem `half.eq_1` of `half` is not generated here: it is defined by \
         well-founded recursion",
    ),
];

/// A definition by pattern matching keeps its type as the header wrote it (`declValEqns`): the
/// pattern columns are the value's `fun`s, so the type's binder names and a function type named
/// by a definition survive, and `#check` prints them. The pin's stdout.
const SIGNATURES: (&str, &str) = (
    "def f : (n : Nat) → Nat
  | 0 => 0
  | k + 1 => k
#check f
def F := Nat → Nat
def g : F
  | 0 => 0
  | _ => 1
#check g
def h (m : Nat) : (n : Nat) → Nat
  | 0 => m
  | _ => 1
#check h
theorem t : (n : Nat) → n + 0 = n
  | 0 => rfl
  | _ + 1 => rfl
#check t
def isZero : Nat → Bool | 0 => true | _ => false
#check isZero
",
    "f (n : Nat) : Nat
g : F
h (m n : Nat) : Nat
t (n : Nat) : n + 0 = n
isZero : Nat → Bool
",
);

#[test]
fn a_definition_by_pattern_matching_keeps_its_written_type() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let (program, expected) = SIGNATURES;
    let (ours, pinned) = run(&lib, &root, HEADER, "signatures", program);
    assert_eq!(
        (ours.code, ours.stdout.as_str()),
        (0, expected),
        "{}",
        ours.stderr
    );
    if let Some(pinned) = pinned {
        assert_eq!(
            (pinned.code, pinned.stdout.as_str()),
            (0, expected),
            "the pin moved"
        );
    }
}

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
        .filter(|lib| lib.join("Init/Core.olean").is_file());
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
        "fln-equation-theorems-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

struct Run {
    code: i32,
    stdout: String,
    stderr: String,
}

/// The installed `lean` on `header` + `program`, and the pinned binary's run when present. The
/// file is named relatively, so diagnostics print as the pin prints them.
fn run(lib: &Path, root: &Path, header: &str, name: &str, program: &str) -> (Run, Option<Run>) {
    let file = format!("{name}.lean");
    let entry = root.join(&file);
    std::fs::write(&entry, format!("{header}{program}")).unwrap();
    let collect = |output: std::process::Output| Run {
        code: output.status.code().expect("normal process exit"),
        stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    };
    let ours = collect(
        Command::new(env!("CARGO_BIN_EXE_lean"))
            .arg(&file)
            .current_dir(root)
            .env("LEAN_PATH", lib)
            .env("FLN_IMPORT_REUSE_DIR", root.join("records"))
            .output()
            .expect("run the installed lean"),
    );
    let theirs = lib
        .parent()
        .and_then(Path::parent)
        .map(|toolchain| toolchain.join("bin/lean"))
        .filter(|lean| lean.is_file())
        .map(|pinned| {
            collect(
                Command::new(pinned)
                    .arg(&file)
                    .current_dir(root)
                    .env("LEAN_PATH", lib)
                    .output()
                    .expect("run the pinned lean"),
            )
        });
    (ours, theirs)
}

#[test]
fn equation_theorems_are_the_pins_and_rewrite_as_the_pin_does() {
    let Some(lib) = pinned_lib() else {
        return;
    };
    let root = workspace();
    let matched = MATCHED
        .iter()
        .map(|(name, program, expected)| (MATCHED_HEADER, name, program, expected));
    let accepted = ACCEPTED
        .iter()
        .map(|(name, program, expected)| (HEADER, name, program, expected));
    for (header, name, program, expected) in accepted.chain(matched) {
        let (ours, pinned) = run(&lib, &root, header, name, program);
        assert_eq!(ours.code, 0, "{name}: {program}\n{}", ours.stderr);
        assert_eq!(&ours.stdout, expected, "{name}");
        if let Some(pinned) = pinned {
            assert_eq!(pinned.code, 0, "{name}: the pinned lean refuses it");
            assert_eq!(&pinned.stdout, expected, "{name}: the pin's stdout moved");
        }
    }
    for (name, program, message) in REFUSED {
        let (ours, pinned) = run(&lib, &root, HEADER, name, program);
        assert_ne!(ours.code, 0, "{name}: accepted {program}");
        assert_ne!(
            ours.code, 5,
            "{name}: a capability refusal\n{}",
            ours.stderr
        );
        assert!(ours.stderr.contains(message), "{name}: {}", ours.stderr);
        if let Some(pinned) = pinned {
            assert_ne!(pinned.code, 0, "{name}: the pinned lean accepts it");
            assert!(pinned.stdout.contains(message), "{name}: {}", pinned.stdout);
        }
    }
    for (name, program, message) in NOT_GENERATED {
        let (ours, pinned) = run(&lib, &root, HEADER, name, program);
        assert_eq!(ours.code, 5, "{name}: {program}\n{}", ours.stderr);
        assert!(ours.stderr.contains(message), "{name}: {}", ours.stderr);
        assert!(ours.stdout.is_empty(), "{name}: {}", ours.stdout);
        if let Some(pinned) = pinned {
            assert_eq!(pinned.code, 0, "{name}: the pinned lean refuses it");
        }
    }
}
