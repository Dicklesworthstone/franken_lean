/-
gen_instance_choices.lean — the pin's instance candidate order and choice (bead fln-vm35).

Run BY THE PINNED REFERENCE BINARY ONLY (D8-2: the Reference as fixture mine), via
scripts/extract/gen_instance_choices.sh, which verifies the binary's commit against
SUITE.lock before trusting a byte of this output.

Usage: lean --run gen_instance_choices.lean <Module>

For every instance in `<Module>`'s import closure, its own type is the goal, as in
FrankenLean's `audit_instance_goal`. One record per goal, tab-separated, sorted by
goal name, deterministic (no timestamps, no paths, no metavariable numbers):

  goal <TAB> priority <TAB> offered <TAB> chosen

- `offered`: `getInstances` (vendored Lean/Meta/SynthInstance.lean:201-240) for the
  goal, comma-separated, in the array's own order: `getUnify`'s traversal order,
  then a stable sort by priority ascending. The generator tries it from the END.
  The goal's own binders add no local instances, so every entry is global.
- `chosen`: the head constant of `synthInstance?`'s answer under default options,
  after the answer's leading lambdas; `-` when there is no answer, and `!` plus the
  exception's first line when the search throws.

A name list never contains a comma, tab or newline: the generator refuses such a
name rather than escaping it.
-/
import Lean
open Lean Meta

def clean (n : Name) : IO String := do
  let s := n.toString (escape := false)
  if s.any (fun c => c == ',' || c == '\t' || c == '\n') then
    throw <| IO.userError s!"unrepresentable name {s}"
  return s

partial def headOf (e : Expr) : Option Name :=
  match e with
  | .lam _ _ b _ => headOf b
  | .mdata _ b => headOf b
  | _ => e.getAppFn.constName?

def record (goal : Name) (entry : InstanceEntry) : MetaM String := do
  let info ← getConstInfo goal
  let offered ← withNewMCtxDepth <| SynthInstance.getInstances info.type
  let mut names := #[]
  for inst in offered do
    match inst.val.getAppFn.constName? with
    | some n => names := names.push (← clean n)
    | none => throwError "a non-constant offered instance for {goal}"
  let chosen ← try
      match ← withNewMCtxDepth (synthInstance? info.type) with
      | some value =>
        match headOf (← instantiateMVars value) with
        | some n => clean n
        | none => pure "?"
      | none => pure "-"
    catch error =>
      let text := (← error.toMessageData.toString).splitOn "\n" |>.headD ""
      pure s!"!{text.replace "\t" " "}"
  return s!"{← clean goal}\t{entry.priority}\t{",".intercalate names.toList}\t{chosen}"

unsafe def main (args : List String) : IO Unit := do
  let [module] := args | throw <| IO.userError "usage: gen_instance_choices.lean <Module>"
  -- The running binary's own library: `findSysroot` would ask whichever `lean` is first
  -- on PATH, which need not be the pin.
  let some sysroot := (← IO.appDir).parent
    | throw <| IO.userError "cannot locate the running binary's toolchain"
  initSearchPath sysroot
  -- Imported extension states, the instance index among them, are built only with
  -- `loadExts`, which needs initializers enabled (hence `unsafe`).
  enableInitializersExecution
  let env ← importModules #[{ module := module.toName }] {} (loadExts := true)
  let state := instanceExtension.getState env
  let goals := state.instanceNames.toList.toArray.qsort (fun a b => Name.lt a.1 b.1)
  let ctx : Core.Context := { fileName := "<instance-choices>", fileMap := default }
  for (goal, entry) in goals do
    let (line, _) ← (record goal entry).run'.toIO ctx { env }
    IO.println line
