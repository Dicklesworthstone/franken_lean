module
prelude
public import Init.Prelude
public meta import Init.Prelude

open Lean

namespace AdmittedLookup
end AdmittedLookup

-- Keep the complete import closure small enough to admit from an empty engine.
-- No user types stand in for Lean.Syntax, Macro.Context or Macro.State.
@[macro Lean.Parser.Term.typeAscription]
public meta def admittedChooseTerm : Macro := fun stx context state =>
  match Lean.Macro.resolveNamespace `AdmittedLookup context state with
  | .ok (.cons _ _) next =>
    match Lean.Macro.resolveGlobalName `Nat context next with
    | .ok (.cons _ _) after => .ok (stx.getArg 1) after
    | .ok .nil after => .error .unsupportedSyntax after
    | .error error after => .error error after
  | .ok .nil next => .error .unsupportedSyntax next
  | .error error next => .error error next

#check (Nat : Bool)
public def admittedMacroValue : Nat := (11 : Bool)
public theorem admittedMacroValue_eq : Eq admittedMacroValue 11 := Eq.refl admittedMacroValue
#check admittedMacroValue
