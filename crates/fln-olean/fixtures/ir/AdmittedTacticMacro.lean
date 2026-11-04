module
prelude
public import Init.Tactics
public meta import Init.Prelude

open Lean
public section

-- A real imported tactic operand is returned without printing or reparsing it.
syntax (name := admittedTactic) "imported_do" "[" tactic "]" : tactic
@[macro admittedTactic]
meta def admittedTacticMacro : Macro := fun stx _ state =>
  .ok (stx.getArg 2) state

-- Later registrations run first. If their expanded tactic fails, evalTactic
-- restores the proof state before trying the earlier registration.
syntax (name := admittedTacticChoice)
  "imported_choice" "[" tactic "]" "[" tactic "]" : tactic
@[macro admittedTacticChoice]
meta def admittedTacticEarlier : Macro := fun stx _ state =>
  .ok (stx.getArg 2) state
@[macro admittedTacticChoice]
meta def admittedTacticLater : Macro := fun stx _ state =>
  .ok (stx.getArg 5) state

syntax (name := admittedTacticFailure) "imported_failure" : tactic
@[macro admittedTacticFailure]
meta def admittedTacticFail : Macro := fun stx _ state =>
  .error (.error stx "imported tactic diagnostic") state

-- A macro failure may fall through to the native tactic elaborator.
@[macro Lean.Parser.Tactic.tacticRfl]
meta def admittedRflFallback : Macro := fun stx _ state =>
  .error (.error stx "the native rfl elaborator must still be tried") state

syntax (name := admittedTacticCallback) "imported_expand" "[" tactic "]" : tactic
@[macro admittedTacticCallback]
meta def admittedTacticExpand : Macro := fun stx context state =>
  match Macro.expandMacro? (stx.getArg 2) context state with
  | .ok (some expanded) next => .ok expanded next
  | .ok none next => .error .unsupportedSyntax next
  | .error error next => .error error next

-- The older looping candidate must remain unexecuted after the later one wins.
syntax (name := admittedTacticLazy) "imported_lazy" "[" tactic "]" : tactic
@[macro admittedTacticLazy]
meta def admittedTacticUnusedLoop : Macro := fun stx _ state => .ok stx state
@[macro admittedTacticLazy]
meta def admittedTacticLazyWinner : Macro := fun stx _ state =>
  .ok (stx.getArg 2) state

syntax (name := admittedTacticLoop) "imported_loop" : tactic
@[macro admittedTacticLoop]
meta def admittedTacticLoopMacro : Macro := fun stx _ state => .ok stx state

syntax (name := admittedTacticTerm) "imported_term" "[" term "]" : term
@[macro admittedTacticTerm]
meta def admittedTacticTermMacro : Macro := fun stx _ state =>
  .ok (stx.getArg 2) state

-- Ordinary quotation-defined user macros use the same imported runtime path.
macro "imported_quoted" : tactic => `(tactic| rfl)
macro "imported_assumption" : tactic => `(tactic| assumption)

-- The quotation's identifier owns its raw substring in the defining module;
-- the native consumer must retain its backing and declaration metadata.
macro "imported_true" : tactic => `(tactic| exact True.intro)
