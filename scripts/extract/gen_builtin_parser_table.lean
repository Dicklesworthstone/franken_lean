/-
gen_builtin_parser_table.lean — Step 1 of fln-generated-builtin-grammar-spike-kcvj.

Extracts the pinned Reference toolchain's builtin parser grammar as a deterministic,
versioned JSONL combinator-AST table:
  * every `Lean.Parser.*` parser-valued definition (`Parser` or `TrailingParser`);
  * every generatable parser-returning helper function in their closure;
  * the strictly verified primitive floor (every `Parser.mk`/`ParserFn` leaf, every
    `ParserFn`-returning helper, and every non-definition type/ctor constant);
  * every `_regBuiltin` registration attaching a builtin parser to its category,
    leading/trailing role, and priority.

D8 status: Reference capacity 2 only (checked-in census/extraction script). Nothing
upstream executes inside FrankenLean; the emitted JSONL is pure versioned data.
-/
import Lean
open Lean Meta Elab

namespace FlnBuiltinParserTable

def sortNames (xs : Array Name) : Array Name :=
  xs.qsort (fun a b => a.toString < b.toString)

def isParserTy (t : Expr) : Bool :=
  t.isConstOf ``Lean.Parser.Parser || t.isConstOf ``Lean.Parser.TrailingParser

def isTrailingParserTy (t : Expr) : Bool :=
  t.isConstOf ``Lean.Parser.TrailingParser

def isParserFnTy (t : Expr) : Bool :=
  t.isConstOf ``Lean.Parser.ParserFn

def returnsParser (t : Expr) : Bool :=
  isParserTy t.getForallBody

def returnsParserFn (t : Expr) : Bool :=
  isParserFnTy t.getForallBody

def forallArity : Expr → Nat
  | .forallE _ _ b _ => 1 + forallArity b
  | .mdata _ e => forallArity e
  | _ => 0

partial def natLit? (e : Expr) : Option Nat :=
  match e.consumeMData with
  | .lit (.natVal n) => some n
  | e =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.appFn!.appArg!.consumeMData with
      | .lit (.natVal n) => some n
      | _ => none
    else if e.isConstOf ``Nat.zero then
      some 0
    else if e.isAppOfArity ``Nat.succ 1 then
      (natLit? e.appArg!).map (· + 1)
    else
      none

partial def exprName? (e : Expr) : Option Name :=
  let e := e.consumeMData
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``Lean.Name.anonymous, #[] => some .anonymous
  | some ``Lean.Name.mkStr, #[p, .lit (.strVal s)] => (exprName? p).map (Name.str · s)
  | some ``Lean.Name.str, #[p, .lit (.strVal s)] => (exprName? p).map (Name.str · s)
  | some ``Lean.Name.mkNum, #[p, n] => do return (← exprName? p).num (← natLit? n)
  | some ``Lean.Name.num, #[p, n] => do return (← exprName? p).num (← natLit? n)
  | some c, args =>
    if c.getPrefix == ``Lean.Name && (c.getString!.startsWith "mkStr") && args.size ≥ 1 then
      args.foldlM (init := Name.anonymous) fun acc a =>
        match a.consumeMData with
        | .lit (.strVal s) => some (acc.str s)
        | _ => none
    else none
  | none, _ => none

partial def exprList? (e : Expr) : Option (List Expr) :=
  let e := e.consumeMData
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``List.nil, _ => some []
  | some ``List.cons, #[_, hd, tl] => (exprList? tl).map (hd :: ·)
  | _, _ => none

def isTypeOrInstanceArg (e : Expr) : Bool :=
  let e := e.consumeMData
  match e with
  | .sort _ | .forallE .. => true
  | _ =>
    match e.getAppFn.constName? with
    | some c =>
      c == ``Unit || c == ``Bool || c == ``Nat || c == ``String || c == ``Int
        || c == ``Lean.Name || c == ``Lean.SyntaxNodeKind || c == ``Lean.Parser.Parser
        || c == ``Lean.Parser.TrailingParser || c == ``Lean.Parser.Token
        || c == ``Lean.Parser.CacheableParserContext || c == ``Lean.Parser.RecoveryContext
        || c == ``List || c == ``Option
        || c.getString!.startsWith "inst"
    | none => false

/-- Normalize a combinator expression into a compact, deterministic JSON AST. -/
partial def exprToAst (env : Environment) (binders : Array String) (e : Expr) : Except String Json := do
  let e := e.consumeMData
  if let some n := natLit? e then
    return Json.mkObj [("lit", "nat"), ("value", n)]
  if let some nm := exprName? e then
    return Json.mkObj [("lit", "name"), ("value", nm.toString)]
  if let some items := exprList? e then
    let astItems ← items.mapM (exprToAst env binders)
    return Json.mkObj [("lit", "list"), ("items", Json.arr astItems.toArray)]
  match e with
  | .bvar idx =>
    if idx < binders.size then
      let name := binders[binders.size - 1 - idx]!
      return Json.mkObj [("var", name), ("idx", idx)]
    else
      return Json.mkObj [("bvar", idx)]
  | .lit (.strVal s) =>
    return Json.mkObj [("lit", "str"), ("value", s)]
  | .lit (.natVal n) =>
    return Json.mkObj [("lit", "nat"), ("value", n)]
  | .const c _ =>
    if c == ``Bool.true then
      return Json.mkObj [("lit", "bool"), ("value", true)]
    if c == ``Bool.false then
      return Json.mkObj [("lit", "bool"), ("value", false)]
    if c == ``Unit.unit then
      return Json.mkObj [("lit", "unit")]
    if c == ``Option.none then
      return Json.mkObj [("op", "none")]
    return Json.mkObj [("const", c.toString)]
  | .lam nm _ body _ =>
    let bname := nm.toString
    let bodyAst ← exprToAst env (binders.push bname) body
    return Json.mkObj [("op", "lam"), ("param", bname), ("body", bodyAst)]
  | .letE nm _ val body _ =>
    let bname := nm.toString
    let valAst ← exprToAst env binders val
    let bodyAst ← exprToAst env (binders.push bname) body
    return Json.mkObj [("op", "let"), ("name", bname), ("val", valAst), ("body", bodyAst)]
  | .sort _ =>
    return Json.mkObj [("type", "Sort")]
  | .forallE .. =>
    return Json.mkObj [("type", "Forall")]
  | .proj s idx st =>
    let stAst ← exprToAst env binders st
    return Json.mkObj [("op", "proj"), ("struct", s.toString), ("idx", idx), ("target", stAst)]
  | .app .. =>
    let fn := e.getAppFn.consumeMData
    let args := e.getAppArgs
    match fn.constName? with
    | some ``HAndThen.hAndThen =>
      if args.size == 6 then
        let lhs ← exprToAst env binders args[4]!
        -- Unwrap constant-Unit thunk `fun _ => rhs` produced by `>>`
        let rhsExpr := match args[5]!.consumeMData with
          | .lam _ _ b _ => if !b.hasLooseBVars then b else args[5]!
          | other => other
        let rhs ← exprToAst env binders rhsExpr
        return Json.mkObj [("op", "seq"), ("lhs", lhs), ("rhs", rhs)]
    | some ``HOrElse.hOrElse =>
      if args.size == 6 then
        let lhs ← exprToAst env binders args[4]!
        let rhsExpr := match args[5]!.consumeMData with
          | .lam _ _ b _ => if !b.hasLooseBVars then b else args[5]!
          | other => other
        let rhs ← exprToAst env binders rhsExpr
        return Json.mkObj [("op", "orelse"), ("lhs", lhs), ("rhs", rhs)]
    | some ``Option.none =>
      return Json.mkObj [("op", "none")]
    | some ``Option.some =>
      if args.size == 2 then
        let v ← exprToAst env binders args[1]!
        return Json.mkObj [("op", "some"), ("value", v)]
    | some ``Char.ofNat =>
      if args.size == 1 then
        if let some code := natLit? args[0]! then
          return Json.mkObj [("lit", "char"), ("code", code)]
    | some ``ite =>
      if args.size == 5 then
        let c ← exprToAst env binders args[1]!
        let t ← exprToAst env binders args[3]!
        let el ← exprToAst env binders args[4]!
        return Json.mkObj [("op", "ite"), ("cond", c), ("then", t), ("else", el)]
    | some ``id =>
      if args.size == 2 then
        return ← exprToAst env binders args[1]!
    | some ``HAppend.hAppend =>
      if args.size == 6 then
        let lhs ← exprToAst env binders args[4]!
        let rhs ← exprToAst env binders args[5]!
        return Json.mkObj [("op", "append"), ("lhs", lhs), ("rhs", rhs)]
    | some ``BEq.beq =>
      if args.size == 4 then
        let lhs ← exprToAst env binders args[2]!
        let rhs ← exprToAst env binders args[3]!
        return Json.mkObj [("op", "beq"), ("lhs", lhs), ("rhs", rhs)]
    | some ``Bool.or =>
      if args.size == 2 then
        let lhs ← exprToAst env binders args[0]!
        let rhs ← exprToAst env binders args[1]!
        return Json.mkObj [("op", "bool_or"), ("lhs", lhs), ("rhs", rhs)]
    | _ => pure ()
    let fnAst ← exprToAst env binders fn
    let mut argAsts : Array Json := #[]
    for a in args do
      if isTypeOrInstanceArg a then
        continue
      argAsts := argAsts.push (← exprToAst env binders a)
    match fn.constName? with
    | some c =>
      return Json.mkObj [("op", "call"), ("fn", c.toString), ("args", Json.arr argAsts)]
    | none =>
      return Json.mkObj [("op", "app"), ("fn", fnAst), ("args", Json.arr argAsts)]
  | .fvar _ => throw "unexpected fvar in closed definition body"
  | .mvar _ => throw "unexpected mvar in closed definition body"
  | .mdata _ inner => exprToAst env binders inner

structure BuiltinReg where
  cat : Name
  leading : Bool
  prio : Nat
  deriving Inhabited

def collectBuiltinRegs (env : Environment) : NameMap (Array BuiltinReg) := Id.run do
  let mut regs : NameMap (Array BuiltinReg) := {}
  for (n, ci) in env.constants.toList do
    if n.components.any (· == `_regBuiltin) then
      if let .defnInfo d := ci then
        let fn := d.value.getAppFn
        let args := d.value.getAppArgs
        if let some head := fn.constName? then
          let isLead := head == ``Lean.Parser.addBuiltinLeadingParser
          let isTrail := head == ``Lean.Parser.addBuiltinTrailingParser
          if (isLead || isTrail) && args.size == 4 then
            if let (some cat, some decl, some prio) := (exprName? args[0]!, exprName? args[1]!, natLit? args[3]!) then
              let cur := (regs.find? decl).getD #[]
              regs := regs.insert decl (cur.push { cat, leading := isLead, prio })
  return regs

def regsToJson (regs : NameMap (Array BuiltinReg)) (n : Name) : Json :=
  let arr := ((regs.find? n).getD #[]).qsort (fun a b =>
    if a.cat != b.cat then a.cat.toString < b.cat.toString
    else if a.leading != b.leading then a.leading && !b.leading
    else a.prio < b.prio)
  Json.arr <| arr.map fun r =>
    Json.mkObj [
      ("cat", r.cat.toString),
      ("leading", r.leading),
      ("prio", r.prio)
    ]

def peelLambdaParams (e : Expr) : Array String × Expr := Id.run do
  let mut cur := e.consumeMData
  let mut params : Array String := #[]
  while true do
    match cur with
    | .lam nm _ body _ =>
      params := params.push nm.toString
      cur := body.consumeMData
    | _ => break
  return (params, cur)

def run : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Lean }] {}
  let regs := collectBuiltinRegs env

  let mut parsers : NameSet := {}
  for (n, ci) in env.constants.toList do
    if (`Lean.Parser).isPrefixOf n then
      if let .defnInfo d := ci then
        if isParserTy d.type then parsers := parsers.insert n

  let mut seen : NameSet := {}
  let mut work : Array Name := parsers.toArray
  let mut directPrim : NameSet := {}
  let mut fnHelperPrim : NameSet := {}
  let mut nonDefnPrim : NameSet := {}
  let mut genHelpers : NameSet := {}

  while !work.isEmpty do
    let n := work.back!
    work := work.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | some (.defnInfo d) =>
      let used := d.value.getUsedConstants
      let usesMkOrFn := used.contains ``Lean.Parser.Parser.mk || used.contains ``Lean.Parser.ParserFn
      let callsParserFnHelper := used.any fun c =>
        match env.find? c with
        | some (.defnInfo dc) => returnsParserFn dc.type
        | _ => false
      if usesMkOrFn || callsParserFnHelper then
        if usesMkOrFn then directPrim := directPrim.insert n
        else fnHelperPrim := fnHelperPrim.insert n
      else
        if !parsers.contains n then genHelpers := genHelpers.insert n
        for c in used do
          if (`Lean.Parser).isPrefixOf c && !seen.contains c then
            match env.find? c with
            | some (.defnInfo dc) =>
              if isParserTy dc.type || returnsParser dc.type then work := work.push c
              else if returnsParserFn dc.type then fnHelperPrim := fnHelperPrim.insert c
              else pure ()
            | some _ => nonDefnPrim := nonDefnPrim.insert c
            | none => pure ()
    | some _ => nonDefnPrim := nonDefnPrim.insert n
    | none => pure ()

  let allPrim := directPrim.union (fnHelperPrim.union nonDefnPrim)
  let genParsers := sortNames <| (parsers.toList.filter (fun n => !allPrim.contains n)).toArray
  let primParsers := sortNames <| (parsers.toList.filter (fun n => allPrim.contains n)).toArray
  let sortedPrims := sortNames allPrim.toArray
  let sortedGenAll := sortNames (genParsers ++ genHelpers.toArray)

  -- Totality check: every Lean.Parser.* parser/helper referenced by any generatable body
  -- must be classified in either allPrim or sortedGenAll.
  let genSet := sortedGenAll.foldl (init := ({} : NameSet)) (·.insert ·)
  for n in sortedGenAll do
    if let some (.defnInfo d) := env.find? n then
      for c in d.value.getUsedConstants do
        if (`Lean.Parser).isPrefixOf c && !allPrim.contains c && !genSet.contains c then
          match env.find? c with
          | some (.defnInfo dc) =>
            if isParserTy dc.type || returnsParser dc.type || returnsParserFn dc.type then
              throw (IO.userError s!"totality violation: {n} references unclassified parser constant {c}")
          | _ => pure ()

  -- Emit header row
  let header := Json.mkObj [
    ("schema", "fln.builtin-parser-table/1"),
    ("kind", "header"),
    ("lean_version", Lean.versionString),
    ("githash", Lean.githash),
    ("closure_size", seen.size),
    ("total_parsers", parsers.size),
    ("generatable_parsers", genParsers.size),
    ("primitive_parsers", primParsers.size),
    ("generatable_helpers", genHelpers.size),
    ("primitive_total", sortedPrims.size),
    ("direct_prim", directPrim.size),
    ("fn_helper_prim", fnHelperPrim.size),
    ("non_defn_prim", nonDefnPrim.size)
  ]
  IO.println header.compress

  -- Emit primitive rows
  for n in sortedPrims do
    let role :=
      if nonDefnPrim.contains n then "type_or_ctor"
      else if fnHelperPrim.contains n then "fn_helper"
      else if parsers.contains n then "parser_def"
      else "combinator"
    let (isTrail, arity, usedLP) :=
      match env.find? n with
      | some (.defnInfo d) =>
        let used := sortNames <| (d.value.getUsedConstants.toList.filter (`Lean.Parser).isPrefixOf).toArray
        (isTrailingParserTy d.type.getForallBody, forallArity d.type, used.map (Json.str ·.toString))
      | some ci =>
        (false, forallArity ci.type, #[])
      | none => (false, 0, #[])
    let row := Json.mkObj [
      ("kind", "primitive"),
      ("name", n.toString),
      ("role", role),
      ("is_trailing", isTrail),
      ("type_arity", arity),
      ("registrations", regsToJson regs n),
      ("used_lean_parser", Json.arr usedLP)
    ]
    IO.println row.compress

  -- Emit generatable parser & helper rows
  for n in sortedGenAll do
    let some (.defnInfo d) := env.find? n
      | throw (IO.userError s!"missing definition for generatable entry {n}")
    let role := if parsers.contains n then "parser_def" else "helper"
    let isTrail := isTrailingParserTy d.type.getForallBody
    let (params, body) := peelLambdaParams d.value
    let ast ← match exprToAst env params body with
      | .ok j => pure j
      | .error msg => throw (IO.userError s!"AST extraction failed on {n}: {msg}")
    let row := Json.mkObj [
      ("kind", "generatable"),
      ("name", n.toString),
      ("role", role),
      ("is_trailing", isTrail),
      ("params", Json.arr (params.map Json.str)),
      ("registrations", regsToJson regs n),
      ("ast", ast)
    ]
    IO.println row.compress

end FlnBuiltinParserTable

def main : IO Unit := FlnBuiltinParserTable.run
