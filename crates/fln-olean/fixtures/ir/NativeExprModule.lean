module
prelude
public import Lean.Expr

public section

open Lean

namespace NativeExpr

@[noinline] def index (e : Expr) : Nat :=
  match e with
  | .bvar n => n
  | _ => 9999999

@[noinline, nospecialize] def useTransform (f : Expr → Expr) (e : Expr) : Expr := f e
@[noinline, nospecialize] def usePredicate (f : Expr → Bool) (e : Expr) : Bool := f e
@[noinline, nospecialize] def useData (f : Expr → UInt64) (e : Expr) : UInt64 := f e

@[noinline] def single (n : Nat) : Nat :=
  let e := Expr.lam .anonymous (.bvar 0) (.app (.bvar 0) (.bvar 1)) .default
  match useTransform (Expr.instantiate1 e) (.bvar n) with
  | .lam _ t (.app f a) _ => index t * 10000 + index f * 100 + index a
  | _ => 9999999

@[noinline] def arrayOrder (n reverse : Nat) : Nat :=
  let e := Expr.app (.bvar 0) (.app (.bvar 1) (.bvar 2))
  let subs := #[Expr.bvar n, Expr.bvar (n + 10)]
  let r := if reverse == 0 then e.instantiate subs else e.instantiateRev subs
  match r with
  | .app f (.app a tail) => index f * 10000 + index a * 100 + index tail
  | _ => 9999999

@[noinline] def lift (s d : Nat) : Nat :=
  let e := Expr.forallE .anonymous (.bvar 0) (.app (.bvar 0) (.bvar 1)) .implicit
  match e.liftLooseBVars s d with
  | .forallE _ t (.app f a) _ => index t * 10000 + index f * 100 + index a
  | _ => 9999999

@[noinline] def contains (i : Nat) : Nat :=
  let e := Expr.letE .anonymous (.bvar 0) (.bvar 2) (.app (.bvar 0) (.bvar 2)) false
  if Expr.hasLooseBVar e i then 1 else 0

@[noinline] def strictEquality (mode : Nat) : Nat :=
  let e := Expr.lam .anonymous (.bvar 0) (.bvar 1) .default
  let other := if mode == 0 then e else Expr.lam .anonymous (.bvar 0) (.bvar 1) .implicit
  if usePredicate (Expr.equal e) other then 1 else 0

@[noinline] def data (n : Nat) : Nat :=
  (useData Expr.data (Expr.app (.bvar n) (.bvar (n + 1)))).toNat

@[noinline] def packData (h range depth flags : Nat) : Nat :=
  (Expr.mkData h.toUInt64 range depth.toUInt32
    (flags % 2 == 1) (flags / 2 % 2 == 1)
    (flags / 4 % 2 == 1) (flags / 8 % 2 == 1)).toNat

@[noinline] def packAppData (f a : Nat) : Nat :=
  (Expr.mkAppData f.toUInt64 a.toUInt64).toNat

end NativeExpr
