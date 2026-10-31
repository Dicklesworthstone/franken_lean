module
prelude
public import Init.Prelude
public meta import Init.Prelude

open Lean

-- Keep the complete import closure small enough to admit from an empty engine.
-- No user types stand in for Lean.Syntax, Macro.Context or Macro.State.
@[macro Lean.Parser.Term.typeAscription]
public meta def admittedChooseTerm : Macro := fun stx _ state =>
  .ok (stx.getArg 1) state

#check (Nat : Bool)
public def admittedMacroValue : Nat := (11 : Bool)
public theorem admittedMacroValue_eq : Eq admittedMacroValue 11 := Eq.refl admittedMacroValue
#check admittedMacroValue
