module
prelude
public import Init
public section

-- A real registered macro with executable control flow, not a quoted template.
macro (name := userChoose) "chooseTerm%" a:term "," b:term : term => do
  if a.raw.getNumArgs == 0 then pure b else pure a

@[noinline] def scopedMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  Lean.Macro.withFreshMacroScope (pure stx)

@[noinline] def errorMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax :=
  throw (Lean.Macro.Exception.error stx "λ\x00error")

-- Demanding an environment method stays outside the first native slice.
@[noinline] def namespaceMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax := do
  let _ ← Lean.Macro.getCurrNamespace
  pure stx
