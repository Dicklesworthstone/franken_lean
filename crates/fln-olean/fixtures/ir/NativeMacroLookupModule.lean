module
prelude
public import Init
public section

-- These are user functions. Their environment-dependent calls must select
-- native Mirror rows rather than interpreting the toolchain implementations.
@[noinline] def lookupNamespaceMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax := do
  let currentNamespace ← Lean.Macro.getCurrNamespace
  pure (.node .none currentNamespace #[stx])

@[noinline] def lookupHasDeclMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax := do
  if ← Lean.Macro.hasDecl stx.getId then
    pure (.atom .none "present")
  else
    pure (.atom .none "absent")
