/-
gen_core_fixtures.lean — C0 micro-fixture generator for fln-core (bead franken_lean-p8a).

Run BY THE PINNED REFERENCE BINARY ONLY (D8-2: the Reference as fixture mine), via
scripts/extract/gen_core_fixtures.sh, which verifies the binary's commit against
SUITE.lock before trusting a byte of this output.

Emits one record per line, '|'-separated, deterministic (no timestamps, no paths):

  string|<label>|<hash>
  name|<label>|<hash>
  level|<label>|<hash>|<depth>|<hasMVar>|<hasParam>|<normHash>
  equiv|<labelA>|<labelB>|<isEquiv>
  expr|<label>|<hash>|<looseBVarRange>|<approxDepth>|<hasFVar>|<hasExprMVar>|<hasLevelMVar>|<hasLevelParam>

The native side (crates/fln-conformance/tests/core_observables.rs) reconstructs every
labeled case with fln-core and diffs each observable. A label unknown to either side
fails the harness — the corpus is closed on both ends.
-/
import Lean
open Lean

def b (v : Bool) : String := if v then "1" else "0"

def emitString (label s : String) : IO Unit :=
  IO.println s!"string|{label}|{s.hash}"

def emitName (label : String) (n : Name) : IO Unit :=
  IO.println s!"name|{label}|{n.hash}"

def emitLevel (label : String) (l : Level) : IO Unit :=
  IO.println s!"level|{label}|{l.hash}|{l.depth}|{b l.hasMVar}|{b l.hasParam}|{l.normalize.hash}"

def emitEquiv (labelA labelB : String) (x y : Level) : IO Unit :=
  IO.println s!"equiv|{labelA}|{labelB}|{b (x.isEquiv y)}"

def emitExpr (label : String) (e : Expr) : IO Unit :=
  IO.println s!"expr|{label}|{e.hash}|{e.looseBVarRange}|{e.approxDepth}|{b e.hasFVar}|{b e.hasExprMVar}|{b e.hasLevelMVar}|{b e.hasLevelParam}"

def main : IO Unit := do
  -- ---- strings (tail lengths 0-8 cross the 8-byte Murmur block boundary) -------------
  emitString "empty" ""
  emitString "a" "a"
  emitString "ab" "ab"
  emitString "abc" "abc"
  emitString "abcd" "abcd"
  emitString "abcde" "abcde"
  emitString "abcdef" "abcdef"
  emitString "abcdefg" "abcdefg"
  emitString "abcdefgh" "abcdefgh"
  emitString "abcdefghi" "abcdefghi"
  emitString "unicode" "héllo€ world"
  emitString "long" (String.join (List.replicate 25 "abcd"))

  -- ---- names -------------------------------------------------------------------------
  emitName "anonymous" .anonymous
  emitName "Lean" (.str .anonymous "Lean")
  emitName "Lean.Meta" (.str (.str .anonymous "Lean") "Meta")
  emitName "Lean.Meta.run" (.str (.str (.str .anonymous "Lean") "Meta") "run")
  emitName "uniq231" (.num (.str .anonymous "_uniq") 231)
  emitName "num0" (.num .anonymous 0)
  emitName "numMax" (.num .anonymous 18446744073709551615)
  emitName "numOverflow" (.num .anonymous 18446744073709551616)
  emitName "mixed" (.num (.str (.num .anonymous 7) "x") 9)

  -- ---- levels ------------------------------------------------------------------------
  let u := Level.param (.str .anonymous "u")
  let v := Level.param (.str .anonymous "v")
  let m := Level.mvar ⟨.num (.str .anonymous "_lmvar") 1⟩
  emitLevel "zero" .zero
  emitLevel "one" (.succ .zero)
  emitLevel "five" (Level.ofNat 5)
  emitLevel "u" u
  emitLevel "v" v
  emitLevel "mvar" m
  emitLevel "succ_u" (.succ u)
  emitLevel "max_u_v" (.max u v)
  emitLevel "max_v_u" (.max v u)
  emitLevel "imax_u_v" (.imax u v)
  emitLevel "imax_u_zero" (.imax u .zero)
  emitLevel "imax_zero_u" (.imax .zero u)
  emitLevel "imax_one_u" (.imax (.succ .zero) u)
  emitLevel "imax_u_u" (.imax u u)
  emitLevel "imax_u_succ_v" (.imax u (.succ v))
  emitLevel "nested_max" (.max (.max u v) v)
  emitLevel "succ_max" (.succ (.max u v))
  emitLevel "max_one_succ_u" (.max (.succ .zero) (.succ u))
  emitLevel "max_three_u" (.max (Level.ofNat 3) u)
  emitLevel "max_u_mvar" (.max u m)
  emitEquiv "max_u_v" "max_v_u" (.max u v) (.max v u)
  emitEquiv "imax_u_zero" "zero" (.imax u .zero) .zero
  emitEquiv "succ_max" "max_succ" (.succ (.max u v)) (.max (.succ u) (.succ v))
  emitEquiv "u" "v" u v

  -- ---- exprs -------------------------------------------------------------------------
  let x := Expr.fvar ⟨.str .anonymous "x"⟩
  let em := Expr.mvar ⟨.str .anonymous "m"⟩
  let natC := Expr.const (.str .anonymous "Nat") []
  let fooC := Expr.const (.str .anonymous "Foo") [.zero, u]
  emitExpr "bvar0" (.bvar 0)
  emitExpr "bvar5" (.bvar 5)
  emitExpr "fvar_x" x
  emitExpr "mvar_m" em
  emitExpr "sort_zero" (.sort .zero)
  emitExpr "sort_u" (.sort u)
  emitExpr "sort_mvar" (.sort m)
  emitExpr "const_Nat" natC
  emitExpr "const_Foo" fooC
  emitExpr "app" (.app natC x)
  emitExpr "app_chain" (.app (.app natC x) em)
  emitExpr "app_bvar" (.app natC (.bvar 9))
  emitExpr "lam_id" (.lam (.str .anonymous "y") natC (.bvar 0) .default)
  emitExpr "lam_loose" (.lam (.str .anonymous "y") natC (.bvar 1) .implicit)
  emitExpr "forall_dom_loose" (.forallE (.str .anonymous "y") (.bvar 0) natC .instImplicit)
  emitExpr "letE" (.letE (.str .anonymous "z") natC (.bvar 2) (.bvar 0) false)
  emitExpr "lit_nat" (.lit (.natVal 42))
  emitExpr "lit_nat_zero" (.lit (.natVal 0))
  emitExpr "lit_nat_big" (.lit (.natVal (2 ^ 80 + 5)))
  emitExpr "lit_str" (.lit (.strVal "hi"))
  emitExpr "mdata" (.mdata default x)
  emitExpr "proj" (.proj (.str .anonymous "Prod") 1 x)
  emitExpr "proj_deep" (.proj (.str .anonymous "Prod") 0 (.app natC (.bvar 3)))
  -- Depth saturation: 300 nested mdata wrappers cap approxDepth at 255.
  let deep := (List.range 300).foldl (fun e _ => Expr.mdata default e) x
  emitExpr "mdata_deep300" deep
  emitExpr "mdata_deep301" (.mdata default deep)
