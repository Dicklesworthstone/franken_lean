module

prelude
public meta import Lean.Elab.Tactic.Basic

public section

open Lean

syntax (name := journalTactic) "journal_tactic%" : tactic

@[macro journalTactic, no_fallback]
meta def stopFallback : Macro := fun stx => pure stx

@[macro journalTactic]
meta def allowFallback : Macro := fun stx => pure stx

@[no_fallback] private meta def privateTagged : Macro := fun stx => pure stx
