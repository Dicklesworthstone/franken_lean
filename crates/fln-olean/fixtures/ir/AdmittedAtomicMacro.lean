module
prelude
public import Init.Tactics
public import Init.Data.Repr
public meta import Init.Prelude

open Lean
public section

def atomicRootValue : Nat := 11
-- Existing declarations deliberately have a different type from the macro's
-- expansion. Bare #check prints the original signature; a parenthesized term
-- instead enters elaboration and runs the macro.
def atomicNat : Bool := true
def atomicType : Bool := false
def atomicFunction (n : Nat) : Nat := n

-- This macro is reached both from written source and from an atomic expansion.
-- Returning its operand preserves the identifier's original source and hygiene.
macro "atomicIdentity!" value:term:max : term => pure value

@[macro ident]
meta def atomicIdentifier : Macro := fun stx =>
  match stx with
  | .ident _ _ (.str .anonymous "atomicNat") _ =>
    do return (← `(Nat.succ (Nat.succ Nat.zero))).raw
  | .ident _ _ (.str .anonymous "atomicType") _ =>
    do return (← `(Nat)).raw
  | .ident _ _ (.str .anonymous "atomicFunction") _ =>
    do return (← `(Nat.succ)).raw
  | .ident _ _ (.str .anonymous "atomicUnknownFunction") _ =>
    do return (← `(Nat.succ)).raw
  | .ident _ _ (.str .anonymous "atomicChain") _ =>
    do return (← `(atomicIdentity! (Nat.succ Nat.zero))).raw
  | .ident _ _ (.str .anonymous "atomicProof") _ =>
    do return (← `(by exact True.intro)).raw
  | .ident _ _ (.str .anonymous "atomicLet") _ =>
    do return (← `(let hidden : Nat := Nat.succ Nat.zero; hidden)).raw
  | .ident _ _ (.str .anonymous "atomicRootProof") _ =>
    do return (← `(Eq.refl atomicRootValue)).raw
  | .ident _ _ (.str .anonymous "atomicLoop") _ => fun _ state => .ok stx state
  | .ident _ _ (.str .anonymous "atomicError") _ =>
    fun _ state => .error (.error stx "imported atomic macro diagnostic") state
  | _ => fun _ state => .error .unsupportedSyntax state

-- A later unsupported candidate must leave the older expansion and native
-- identifier elaboration available, without treating diagnostics as fallback.
@[macro ident]
meta def atomicTryNext : Macro := fun _ _ state => .error .unsupportedSyntax state

namespace AtomicScope

@[scoped macro ident]
meta def atomicScopedIdentifier : Macro := fun stx =>
  match stx with
  | .ident _ _ (.str .anonymous "atomicNat") _ =>
    do return (← `(Nat.succ Nat.zero)).raw
  | _ => fun _ state => .error .unsupportedSyntax state

end AtomicScope
