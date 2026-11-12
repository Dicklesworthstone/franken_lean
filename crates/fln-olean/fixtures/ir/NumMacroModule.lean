module
prelude
public import Init
public import Lean.Syntax
import all Init.Prelude
public section

-- User-owned MacroM code exercises the public literal APIs rather than the
-- private recursive decoders that the pin implements them with.
@[noinline] def spelledNumberMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure (Lean.Syntax.mkNumLit stx.getAtomVal stx.getHeadInfo).raw

@[noinline] def normalizeNumberMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  match stx.isNatLit? with
  | some value => pure (Lean.Syntax.mkNatLit value stx.getHeadInfo).raw
  | none => pure .missing

@[noinline] def typedNumberMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure (Lean.Syntax.mkNatLit (Lean.TSyntax.getNat ⟨stx⟩) stx.getHeadInfo).raw

@[noinline] def quotedNumberMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure (Lean.quote (Lean.TSyntax.getNat ⟨stx⟩) : Lean.NumLit).raw

@[noinline] def hugeNaturalMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  pure (Lean.Syntax.mkNatLit
    115792089237316195423570985008687907853269984665640564039457584007913129639937
    stx.getHeadInfo).raw

syntax (name := numIncrement) "numIncrement% " num : term
@[macro numIncrement] meta def expandNumIncrement : Lean.Macro
  | `(numIncrement% $n:num) => pure (Lean.Syntax.mkNatLit (n.getNat + 1)).raw
  | _ => Lean.Macro.throwUnsupported

-- These ordinary source uses also run while the pin emits the user IR.
@[expose] def nativeNumberSmall : Nat := numIncrement% 0xff
@[expose] def nativeNumberWide : Nat := numIncrement% 18446744073709551615
example : nativeNumberSmall = 256 := rfl
example : nativeNumberWide = 18446744073709551616 := rfl
