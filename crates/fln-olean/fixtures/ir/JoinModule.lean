module

public section

-- Generated with the Reference pinned in SUITE.lock (Lean v4.32.0).
-- The retained IR exercises ordinary compiler-created join points and a
-- projection in a separately compiled function with an unknown caller shape.
set_option trace.compiler.ir.result true

@[noinline] def joinChoice (b : Bool) (n : Nat) : Nat :=
  let x := if b then n + 2 else n + 5
  x * 3

@[noinline] def joinNested (a b : Bool) (n : Nat) : Nat :=
  let x := if a then n + 7 else n + 13
  let y := if b then x * 3 else x * 5
  y + n

@[noinline] def secondField (p : Nat × String) : String := p.2

def fieldAnswer : String := secondField (19, "retained λ 🦀")
