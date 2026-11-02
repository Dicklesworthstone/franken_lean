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

@[noinline] def lookupResolveNamespaceMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax := do
  let candidates ← Lean.Macro.resolveNamespace stx.getId
  match candidates with
  | [] => pure (.atom .none "absent")
  | [first] => pure (.node .none first #[stx])
  | first :: second :: _ => pure (.node .none first #[.node .none second #[stx]])

@[noinline] def lookupResolveGlobalMacro (stx : Lean.Syntax) : Lean.MacroM Lean.Syntax := do
  let candidates ← Lean.Macro.resolveGlobalName stx.getId
  match candidates with
  | [] => pure (.atom .none "absent")
  | [(target, [])] => pure (.node .none target #[stx])
  | [(target, field :: _)] => pure (.node .none target #[.atom .none field])
  | (first, _) :: (second, _) :: _ => pure (.node .none first #[.node .none second #[stx]])
