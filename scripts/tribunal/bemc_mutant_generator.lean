/-
Reject-side mutant generator for the kernel differential
(bead `fln-kernel-reject-side-at-scale-bemc`).

Runs ONLY under the stock pinned Reference binary, inside the Tribunal, as a
differential oracle under D8: it loads a target module's environment, mutates
sampled declarations at the `Expr` level, asks the PIN's kernel for a verdict
on every mutant under a fresh name, and persists the whole batch — including
kernel-REJECTED mutants — as a synthetic module via `doCheck := false`, so the
FrankenLean side can judge the identical bytes independently. It is never a
FrankenLean runtime component.

Usage (pinned binary):
  lean --run scripts/tribunal/bemc_mutant_generator.lean \
    <TargetModule> <seed> <mutantsPerDecl> <maxDecls> <outDir>

Outputs in <outDir>:
  <TargetModule>.bemc.olean   — the synthetic module (imports the target only)
  <TargetModule>.bemc.tsv     — one row per mutant:
      origin  fresh  operator  pin_verdict  pin_class

Operator table (grows toward the bead's full list; each anchors the
KERNEL_CONTRACT.md rule family it aims at):
  swap_args      — swap the two arguments of a sampled 2-ary application
                   (application typing, KR-2xx app rules)
  bump_univ      — `u` becomes `u+1` at a sampled sort (universe discipline,
                   KR-30x sort/level rules)
  nat_lit        — a sampled Nat literal changes value (literal typing and
                   defeq, KR-31x literal rules)
-/
import Lean

open Lean Meta

def exKind : Kernel.Exception → String
  | .unknownConstant .. => "unknownConstant"
  | .alreadyDeclared .. => "alreadyDeclared"
  | .declTypeMismatch .. => "declTypeMismatch"
  | .declHasMVars .. => "declHasMVars"
  | .declHasFVars .. => "declHasFVars"
  | .funExpected .. => "funExpected"
  | .typeExpected .. => "typeExpected"
  | .letTypeMismatch .. => "letTypeMismatch"
  | .exprTypeMismatch .. => "exprTypeMismatch"
  | .appTypeMismatch .. => "appTypeMismatch"
  | .invalidProj .. => "invalidProj"
  | .thmTypeIsNotProp .. => "thmTypeIsNotProp"
  | .other msg => s!"other:{msg.takeWhile (· ≠ '\n')}"
  | .deterministicTimeout => "deterministicTimeout"
  | .excessiveMemory => "excessiveMemory"
  | .deepRecursion => "deepRecursion"
  | .interrupted => "interrupted"

/-- Deterministic site counter: how many sites an operator could hit. The
sampler picks a site index first, then the rewriter targets exactly that
site, so one (seed, declaration, operator) names one mutant. -/
partial def countSites (pick : Expr → Bool) : Expr → Nat
  | e@(.app f a) => (if pick e then 1 else 0) + countSites pick f + countSites pick a
  | e@(.lam _ t v _) => (if pick e then 1 else 0) + countSites pick t + countSites pick v
  | e@(.forallE _ t v _) => (if pick e then 1 else 0) + countSites pick t + countSites pick v
  | e@(.letE _ t v b _) =>
    (if pick e then 1 else 0) + countSites pick t + countSites pick v + countSites pick b
  | e@(.mdata _ i) => (if pick e then 1 else 0) + countSites pick i
  | e@(.proj _ _ i) => (if pick e then 1 else 0) + countSites pick i
  | e => if pick e then 1 else 0

/-- Rewrite the `n`-th site (pre-order) that `pick` admits, with `rw`. Returns
`none` when fewer than `n + 1` sites exist. State is the countdown. -/
partial def rewriteSite (pick : Expr → Bool) (rw : Expr → Expr) :
    Expr → Nat → Option (Expr × Nat)
  | e, n =>
    let step (e : Expr) (n : Nat) : Option (Expr × Nat) :=
      match e with
      | .app f a =>
        match rewriteSite pick rw f n with
        | some (f', n') => some (.app f' a, n')
        | none =>
          match rewriteSite pick rw a n with
          | some (a', n') => some (.app f a', n')
          | none => none
      | .lam nm t v i =>
        match rewriteSite pick rw t n with
        | some (t', n') => some (.lam nm t' v i, n')
        | none =>
          match rewriteSite pick rw v n with
          | some (v', n') => some (.lam nm t v' i, n')
          | none => none
      | .forallE nm t v i =>
        match rewriteSite pick rw t n with
        | some (t', n') => some (.forallE nm t' v i, n')
        | none =>
          match rewriteSite pick rw v n with
          | some (v', n') => some (.forallE nm t v' i, n')
          | none => none
      | .letE nm t v b nd =>
        match rewriteSite pick rw t n with
        | some (t', n') => some (.letE nm t' v b nd, n')
        | none =>
          match rewriteSite pick rw v n with
          | some (v', n') => some (.letE nm t v' b nd, n')
          | none =>
            match rewriteSite pick rw b n with
            | some (b', n') => some (.letE nm t v b' nd, n')
            | none => none
      | .mdata m i =>
        (rewriteSite pick rw i n).map (fun (i', n') => (.mdata m i', n'))
      | .proj s ix i =>
        (rewriteSite pick rw i n).map (fun (i', n') => (.proj s ix i', n'))
      | _ => none
    if pick e then
      if n == 0 then some (rw e, 0)
      else
        match step e (n - 1) with
        | some (e', n') => some (e', n' + 1)
        | none => none
    else step e n

structure Op where
  name : String
  pick : Expr → Bool
  rw : Expr → Expr

def ops : Array Op := #[
  { name := "swap_args"
    pick := fun e => match e with | .app (.app _ _) _ => true | _ => false
    rw := fun e => match e with
      | .app (.app f a) b => .app (.app f b) a
      | e => e },
  { name := "bump_univ"
    pick := fun e => match e with | .sort _ => true | _ => false
    rw := fun e => match e with
      | .sort u => .sort (.succ u)
      | e => e },
  { name := "nat_lit"
    pick := fun e => match e with | .lit (.natVal _) => true | _ => false
    rw := fun e => match e with
      | .lit (.natVal v) => .lit (.natVal (v + 1))
      | e => e }
]

structure Row where
  origin : Name
  fresh : Name
  op : String
  verdict : String
  cls : String

def rowLine (r : Row) : String :=
  s!"{r.origin}\t{r.fresh}\t{r.op}\t{r.verdict}\t{r.cls}"

unsafe def run (target : Name) (seed mutantsPerDecl maxDecls : Nat)
    (outDir : System.FilePath) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := target }] {}
  -- Deterministic declaration sample: name-sorted theorems and definitions
  -- the TARGET MODULE ITSELF declares. Every imported constant has a module
  -- index, so presence alone matched the whole closure (the first run drew
  -- Add.* from Init.Prelude alphabetically); the filter compares against the
  -- target's own index.
  let some targetIdx := env.getModuleIdx? target
    | throw <| IO.userError s!"module {target} not found in its own import closure"
  let owned := env.constants.toList.filter fun (n, ci) =>
    (env.getModuleIdxFor? n == some targetIdx)
      |>.and (match ci with | .thmInfo _ => true | .defnInfo _ => true | _ => false)
      |>.and (!n.isInternal)
  let sorted := (owned.toArray.qsort (fun a b => a.1.toString < b.1.toString)).toList
  let chosen := sorted.take maxDecls
  IO.FS.createDirAll outDir
  let mut rows : Array Row := #[]
  let mut transport := env
  let mut rng := mkStdGen seed
  let mut idx := 0
  for (n, ci) in chosen do
    let value := match ci.value? with
      | some v => v
      | none => ci.type
    for _ in [0:mutantsPerDecl] do
      idx := idx + 1
      -- operator, then a site within its site count, both from the seeded RNG
      let (opIx, rng') := randNat rng 0 (ops.size - 1)
      rng := rng'
      let some op := ops[opIx]? | continue
      let sites := countSites op.pick value
      if sites == 0 then
        continue
      let (siteIx, rng'') := randNat rng 0 (sites - 1)
      rng := rng''
      let some (mutated, _) := rewriteSite op.pick op.rw value siteIx
        | continue
      if mutated == value then
        continue
      let fresh := Name.str n s!"_bemc_{idx}"
      -- preserve the declaration kind: a def mutant stays a def (hints and
      -- safety carried), a theorem mutant stays a theorem. Wrapping defs as
      -- theorems made every def mutant die at thmTypeIsNotProp before the
      -- mutation was examined — a vacuous reject class (first-run finding).
      let decl : Declaration := match ci with
        | .defnInfo d => .defnDecl { d with name := fresh, value := mutated }
        | _ => .thmDecl {
            name := fresh
            levelParams := ci.levelParams
            type := ci.type
            value := mutated
          }
      let (verdict, cls) :=
        match env.addDeclCore 0 decl none (doCheck := true) with
        | .ok _ => ("accept", "")
        | .error e => ("reject", exKind e)
      rows := rows.push { origin := n, fresh, op := op.name, verdict, cls }
      -- every judged mutant rides in the synthetic module, unchecked
      match transport.addDeclCore 0 decl none (doCheck := false) with
      | .ok t => transport := t
      | .error e =>
        rows := rows.push
          { origin := n, fresh, op := op.name
            verdict := "transport-failed", cls := exKind e }
  -- The synthetic module lives under the `Bemc` prefix so the FrankenLean
  -- harness can route it with one extra root entry, and its on-disk path
  -- mirrors its module name component-for-component (the name↔path law every
  -- olean root obeys). String concatenation, never withExtension: a dotted
  -- module name's last component reads as an extension and is silently
  -- replaced (first-run finding: Init.Data.Nat.Basic wrote
  -- Init.Data.Nat.bemc.olean).
  let syntheticName := (`Bemc).append target
  let sealed := transport.setMainModule syntheticName
  let relative := syntheticName.toString.replace "." "/"
  let oleanPath := outDir / s!"{relative}.olean"
  let tsvPath := outDir / s!"{relative}.tsv"
  if let some parent := oleanPath.parent then
    IO.FS.createDirAll parent
  writeModule sealed oleanPath (writeIR := false)
  let tsv := String.intercalate "\n" (rows.toList.map rowLine)
  IO.FS.writeFile tsvPath (tsv ++ "\n")
  let rejects := rows.filter (·.verdict == "reject") |>.size
  let accepts := rows.filter (·.verdict == "accept") |>.size
  IO.println s!"bemc-generator module={target} decls={chosen.length} mutants={rows.size} \
pin_reject={rejects} pin_accept={accepts} seed={seed}"

unsafe def main (args : List String) : IO Unit := do
  match args with
  | [target, seed, perDecl, maxDecls, outDir] =>
    run target.toName seed.toNat! perDecl.toNat! maxDecls.toNat! ⟨outDir⟩
  | _ =>
    throw <| IO.userError
      "usage: bemc_mutant_generator <TargetModule> <seed> <mutantsPerDecl> <maxDecls> <outDir>"
