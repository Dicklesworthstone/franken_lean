module
prelude
public import Init
public section

-- Every callable is discovered through the emitted macro journal. The outer
-- macros call the real MacroM method rather than returning an inner syntax for
-- a later tree walk to discover. Their children retain the caller's source.
syntax (name := recursiveInner) "recursiveInner%" term "," term : term
macro_rules (kind := recursiveInner)
  | stx => pure (stx.getArg 1)

namespace RecursiveScope
scoped macro_rules (kind := recursiveInner)
  | stx => pure (stx.getArg 3)
end RecursiveScope

syntax (name := recursiveOuter) "recursiveOuter%" term "," term : term
macro_rules (kind := recursiveOuter)
  | stx => do
    match ← Lean.Macro.expandMacro? (stx.setKind `recursiveInner) with
    | some expanded => pure expanded
    | none => throw Lean.Macro.Exception.unsupportedSyntax

syntax (name := recursiveNone) "recursiveNone%" term : term
macro_rules (kind := recursiveNone)
  | stx => do
    match ← Lean.Macro.expandMacro? (stx.setKind `recursiveUnregistered) with
    | some expanded => pure expanded
    | none => pure (stx.getArg 1)

syntax (name := recursiveNever) "recursiveNever%" term : term
macro_rules (kind := recursiveNever)
  | _stx => throw Lean.Macro.Exception.unsupportedSyntax

syntax (name := recursiveUnsupported) "recursiveUnsupported%" term : term
macro_rules (kind := recursiveUnsupported)
  | stx => do
    match ← Lean.Macro.expandMacro? (stx.setKind `recursiveNever) with
    | some expanded => pure expanded
    | none => pure (stx.getArg 1)

syntax (name := recursiveFailure) "recursiveFailure%" term : term
macro_rules (kind := recursiveFailure)
  | stx => throw (Lean.Macro.Exception.error stx "recursive fixture failure")

syntax (name := recursiveErrorOuter) "recursiveErrorOuter%" term : term
macro_rules (kind := recursiveErrorOuter)
  | stx => do
    match ← Lean.Macro.expandMacro? (stx.setKind `recursiveFailure) with
    | some expanded => pure expanded
    | none => throw Lean.Macro.Exception.unsupportedSyntax

#eval recursiveOuter% 10, 20
section
open scoped RecursiveScope
#eval recursiveOuter% 10, 20
end
#eval recursiveOuter% 10, 20
#eval recursiveNone% 30
#eval recursiveUnsupported% 40
