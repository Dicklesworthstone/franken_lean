module
prelude
public import Lean.Expr
public import Lean.Util.FindExpr
public import Lean.Util.ReplaceExpr

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

@[noinline, nospecialize] def useFinder
    (f : Expr → Option Expr) (e : Expr) : Option Expr := f e

@[noinline] def nameCode : Name → Nat
  | .anonymous => 0
  | .num p n => 1 + n + 17 * nameCode p
  | .str p _ => 1000 + nameCode p

@[noinline] def binderCode : BinderInfo → Nat
  | .default => 0
  | .implicit => 1
  | .strictImplicit => 2
  | .instImplicit => 3

@[noinline] def metadataCode (m : MData) : Nat :=
  match m.entries with
  | [(name, .ofNat n)] => 1 + nameCode name + 17 * n
  | _ => 0

-- A user-defined observer avoids replacing the traversal under test with
-- another imported toolchain implementation, including metadata equality.
@[noinline] def fingerprint : Expr → Nat
  | .bvar n => 100 + n
  | .fvar id => 200 + nameCode id.name
  | .mvar id => 300 + nameCode id.name
  | .sort .zero => 400
  | .sort _ => 401
  | .const name _ => 500 + nameCode name
  | .app f a => 600 + 13 * fingerprint f + 17 * fingerprint a
  | .lam name t b bi =>
    700 + nameCode name + 13 * fingerprint t + 17 * fingerprint b + binderCode bi
  | .forallE name t b bi =>
    800 + nameCode name + 13 * fingerprint t + 17 * fingerprint b + binderCode bi
  | .letE name t v b nondep =>
    900 + nameCode name + 11 * fingerprint t + 13 * fingerprint v +
      17 * fingerprint b + (if nondep then 1 else 0)
  | .lit (.natVal n) => 1000 + n
  | .lit (.strVal _) => 1001
  | .mdata m e => 1100 + metadataCode m + 17 * fingerprint e
  | .proj name i e => 1200 + nameCode name + 13 * i + 17 * fingerprint e

@[noinline] def optionFingerprint : Option Expr → Nat
  | none => 9999999
  | some e => fingerprint e

@[noinline] def node (kind n : Nat) : Expr :=
  let name := Name.num .anonymous n
  match kind with
  | 0 => .bvar n
  | 1 => .fvar ⟨name⟩
  | 2 => .mvar ⟨name⟩
  | 3 => .sort (.succ .zero)
  | 4 => .const name []
  | 5 => .app (.bvar n) (.bvar (n + 1))
  | 6 => .lam name (.bvar n) (.bvar (n + 1)) .strictImplicit
  | 7 => .forallE name (.bvar n) (.bvar (n + 1)) .instImplicit
  | 8 => .letE name (.bvar n) (.bvar (n + 1)) (.bvar (n + 2)) true
  | 9 => .lit (.natVal n)
  | 10 => .mdata ⟨[(name, .ofNat n)]⟩ (.bvar n)
  | _ => .proj name (n + 2) (.bvar n)

@[noinline] def shared (n : Nat) : Expr :=
  let child := Expr.app (.bvar n) (.bvar (n + 1))
  .app child child

@[noinline] def rewrite (needle replacement mode : Nat) (e : Expr) : Option Expr :=
  match e with
  | .app _ _ =>
    if mode == 1 then some (.app (.bvar needle) (.bvar replacement)) else none
  | .bvar n => if n == needle then some (.bvar replacement) else none
  | _ => none

@[noinline] def unchanged (_ : Expr) : Option Expr := none
@[noinline] def replaceRoot (n : Nat) (_ : Expr) : Option Expr := some (.bvar n)

@[noinline] def replaceDirect (n mode : Nat) : Nat :=
  fingerprint (Expr.replaceImpl (rewrite n (n + 10) mode) (shared n))

@[noinline] def replaceCaptured (n mode : Nat) : Nat :=
  fingerprint (useTransform (Expr.replaceImpl (rewrite n (n + 10) mode)) (shared n))

@[noinline] def replaceKinds (kind n mode : Nat) : Nat :=
  let e := node kind n
  let r := if mode == 0 then Expr.replaceImpl unchanged e
    else if mode == 1 then Expr.replaceImpl (replaceRoot (n + 10)) e
    else Expr.replaceImpl (rewrite n (n + 10) 0) e
  fingerprint r

@[noinline] def replaceData (n : Nat) : Nat :=
  (Expr.data (Expr.replaceImpl (rewrite n (n + 10) 0) (shared n))).toNat

@[noinline] def search (needle mode : Nat) (e : Expr) : Bool :=
  match e with
  | .app _ _ => mode == 0
  | .bvar n => mode == 1 || n == needle
  | _ => false

@[noinline] def findDirect (n needle mode : Nat) : Nat :=
  optionFingerprint (Expr.findImpl? (search needle mode) (shared n))

@[noinline] def findCaptured (n needle mode : Nat) : Nat :=
  optionFingerprint (useFinder (Expr.findImpl? (search needle mode)) (shared n))

@[noinline] def extendedSearch (needle mode : Nat) (e : Expr) : Expr.FindStep :=
  match e with
  | .lam _ _ _ _ => if mode == 1 then .done else .visit
  | .app (.bvar _) _ => if mode == 2 then .found else .visit
  | .app _ _ => if mode == 4 then .found else .visit
  | .bvar n => if mode == 3 || n == needle then .found else .visit
  | _ => .visit

@[noinline] def searchTree (n mode : Nat) : Expr :=
  if mode == 0 then .app (.app (.bvar n) (.bvar (n + 1))) (.bvar (n + 2))
  else .app (.lam .anonymous (.bvar n) (.bvar (n + 1)) .implicit) (.bvar (n + 2))

@[noinline] def findExtDirect (n needle mode tree : Nat) : Nat :=
  optionFingerprint (Expr.findExtImpl? (extendedSearch needle mode) (searchTree n tree))

@[noinline] def findExtCaptured (n needle mode tree : Nat) : Nat :=
  optionFingerprint
    (useFinder (Expr.findExtImpl? (extendedSearch needle mode)) (searchTree n tree))

@[noinline] def partialApplication (e : Expr) : Bool :=
  match e with
  | .app (.bvar _) _ => true
  | _ => false

@[noinline] def findPartialApplication (n : Nat) : Nat :=
  optionFingerprint (Expr.findImpl? partialApplication (searchTree n 0))

end NativeExpr
