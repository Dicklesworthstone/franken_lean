/-
gen_grammar_census.lean — the pin's builtin grammar, and the syntax Init/Std declare and use
(bead fln-vokf; plan §9.1; Rules D5/D8-2: derived from the pin, never transcribed).

Run only by scripts/extract/gen_grammar_census.sh, which locates the pinned Reference
binary, verifies its commit against SUITE.lock, and adds the provenance header. The
Reference participates here in exactly one legal capacity: census mine through a checked-in
extraction script. Nothing here is a FrankenLean runtime component.

Modes:

  grammar
    Every builtin registration compiled into the pinned binary, read from the `_regBuiltin`
    declarations `declareBuiltin` leaves in the environment (`Lean/Compiler/InitAttr.lean`):
      * builtin parsers (`addBuiltinLeadingParser`/`addBuiltinTrailingParser`): category,
        leading/trailing, priority, the precedence(s) of the parser's own `leadingNode` /
        `trailingNode`, `firstTokens`, and the tokens `ParserInfo.collectTokens` reports;
      * keyed builtin registrations (`KeyedDeclsAttribute.addBuiltin`): the builtin attribute,
        the syntax kind (key) and the handler;
      * every other `_regBuiltin` family, counted.
    Then the runtime tables the binary itself built (`builtinTokenTable`,
    `builtinSyntaxNodeKindSetRef`, `builtinParserCategoriesRef`), the module-header parser's
    tokens and kinds, the named special kinds (constants of type `SyntaxNodeKind`), and, for
    every Init/Std module, its imports, its parser-extension entries (tokens, kinds, parsers,
    categories), the syntax declarations it compiles (ParserDescr constants, with precedence
    and the tokens their compiled parser collects), and its `macro` attribute entries. For
    every other module only the kind and category entries are recorded, because Init/Std parse
    trees contain nodes Lean.* parsers build (the Verso docstring grammar).
    Totality is checked HERE, against the oracle's own runtime state, and a failure exits 3
    instead of emitting a census:
      * each builtin category's registered declaration set equals the `_regBuiltin` parser rows;
      * the runtime builtin token table equals the union of those parsers' collected tokens;
      * for a fixed sample of modules, the token table `importModules` builds equals the
        builtin table plus the global token entries of the module's transitive import closure.

  replay <path> <module>
    One source file is replayed through the pinned frontend as `lean` builds it (header, then
    `IO.processCommands`), and the record names every syntax node kind its commands' parse
    trees contain, the error count (a faithful replay has zero), and every syntax-extension
    command with its line. One file per process: see `replay` for why.

Output is deterministic: every collection is sorted before printing; no paths, times or
addresses are emitted except the vendor-relative source path the caller supplies.
-/
import Lean
open Lean Meta Elab

/-! ## Rendering -/

def render (n : Name) : String := toString n

def sortStrings (xs : Array String) : Array String := xs.qsort (· < ·)

def dedupSorted (xs : Array String) : Array String := Id.run do
  let mut out : Array String := #[]
  for x in sortStrings xs do
    if out.back? != some x then out := out.push x
  return out

/-- A token is printed inside a space-separated field, so whitespace or a tab inside one would
make the census ambiguous. None exists at the pin; meeting one is a refusal, not an escape. -/
def checkToken (tk : String) : IO String := do
  if tk.isEmpty || tk.any (fun c => c.isWhitespace || c.toNat < 0x20) then
    throw (IO.userError s!"census refusal: token {repr tk} cannot be printed unambiguously")
  return tk

def joinTokens (tks : List String) : IO String := do
  let tks ← tks.toArray.mapM checkToken
  return " ".intercalate (dedupSorted tks).toList

/-! ## Decoding `toExpr` encodings found in `_regBuiltin` values -/

partial def exprName? (e : Expr) : Option Name :=
  let e := e.consumeMData
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``Lean.Name.anonymous, #[] => some .anonymous
  | some ``Lean.Name.mkStr, #[p, .lit (.strVal s)] => (exprName? p).map (Name.str · s)
  | some ``Lean.Name.str, #[p, .lit (.strVal s)] => (exprName? p).map (Name.str · s)
  | some ``Lean.Name.mkNum, #[p, n] => do (← exprName? p).num (← natLit? n)
  | some ``Lean.Name.num, #[p, n] => do (← exprName? p).num (← natLit? n)
  | some c, args =>
    if c.getPrefix == ``Lean.Name && (c.getString!.startsWith "mkStr") && args.size ≥ 1 then
      args.foldlM (init := Name.anonymous) fun acc a =>
        match a.consumeMData with
        | .lit (.strVal s) => some (acc.str s)
        | _ => none
    else none
  | none, _ => none
where
  natLit? (e : Expr) : Option Nat :=
    match e.consumeMData with
    | .lit (.natVal n) => some n
    | e => if e.isAppOfArity ``OfNat.ofNat 3 then
        match e.appFn!.appArg!.consumeMData with
        | .lit (.natVal n) => some n
        | _ => none
      else none

def rawNat? (e : Expr) : Option Nat := exprName?.natLit? e

/-! ## The `_regBuiltin` declarations -/

def isRegBuiltin (n : Name) : Bool :=
  n.components.any fun c => c == `_regBuiltin

inductive Registration where
  | parser (cat decl : Name) (leading : Bool) (prio : Nat)
  | keyed (attr key decl : Name)
  | other (family : Name)

def classify (reg : Name) (value : Expr) : IO Registration := do
  let fn := value.getAppFn
  let args := value.getAppArgs
  let some head := fn.constName?
    | throw (IO.userError s!"census refusal: {reg} is not an application of a constant")
  let refuse (what : String) : IO Registration :=
    throw (IO.userError s!"census refusal: {reg} ({head}) has an undecodable {what}")
  if head == ``Lean.Parser.addBuiltinLeadingParser || head == ``Lean.Parser.addBuiltinTrailingParser then
    let #[cat, decl, _, prio] := args | refuse "argument list"
    let some cat := exprName? cat | refuse "category"
    let some decl := exprName? decl | refuse "declaration name"
    let some prio := rawNat? prio | refuse "priority"
    return .parser cat decl (head == ``Lean.Parser.addBuiltinLeadingParser) prio
  else if head == ``Lean.KeyedDeclsAttribute.addBuiltin then
    let #[_, attr, key, decl, _] := args | refuse "argument list"
    let some attr := attr.constName? | refuse "attribute"
    let some key := exprName? key | refuse "key"
    let some decl := exprName? decl | refuse "declaration name"
    return .keyed attr key decl
  else
    return .other head

/-! ## Precedence of a builtin parser's own node -/

/-- The first `leadingNode k prec p` / `trailingNode k prec lhsPrec p` whose kind is the
declaration itself, i.e. the node `leading_parser`/`trailing_parser` builds for it. -/
partial def ownNode? (decl : Name) (e : Expr) : Option (Bool × Array Expr) :=
  let here : Option (Bool × Array Expr) :=
    if e.isAppOfArity ``Lean.Parser.leadingNode 3 && exprName? e.appFn!.appFn!.appArg! == some decl then
      some (true, e.getAppArgs)
    else if e.isAppOfArity ``Lean.Parser.trailingNode 4 &&
        exprName? e.appFn!.appFn!.appFn!.appArg! == some decl then
      some (false, e.getAppArgs)
    else none
  here.orElse fun _ => match e with
    | .app f a => (ownNode? decl f).orElse fun _ => ownNode? decl a
    | .lam _ t b _ => (ownNode? decl t).orElse fun _ => ownNode? decl b
    | .forallE _ t b _ => (ownNode? decl t).orElse fun _ => ownNode? decl b
    | .letE _ t v b _ =>
      ((ownNode? decl t).orElse fun _ => ownNode? decl v).orElse fun _ => ownNode? decl b
    | .mdata _ b => ownNode? decl b
    | .proj _ _ b => ownNode? decl b
    | _ => none

def evalPrec (env : Environment) (e : Expr) : IO Nat := do
  let r ← (MetaM.run' (do
      let w ← whnf e
      match ← evalNat w with
      | some n => pure (some n)
      | none => pure (← evalNat (← reduce e))) : CoreM (Option Nat)).toIO
    { fileName := "<census>", fileMap := default, maxHeartbeats := 0 } { env }
  match r.1 with
  | some n => return n
  | none => throw (IO.userError s!"census refusal: precedence {e} does not evaluate to a numeral")

structure PrecInfo where
  prec : Option Nat := none
  lhsPrec : Option Nat := none

def precOf (env : Environment) (decl : Name) : IO PrecInfo := do
  let some info := env.find? decl | throw (IO.userError s!"census refusal: no constant {decl}")
  let some value := info.value? (allowOpaque := true) | return {}
  match ownNode? decl value with
  | none => return {}
  | some (true, args) => return { prec := some (← evalPrec env args[1]!) }
  | some (false, args) =>
    return { prec := some (← evalPrec env args[1]!), lhsPrec := some (← evalPrec env args[2]!) }

/-- The precedence a `syntax`/`notation`/`infix` declaration compiled into its top-level
`ParserDescr.node k prec d` / `ParserDescr.trailingNode k prec lhsPrec d`. -/
def descrPrecOf (env : Environment) (decl : Name) : IO PrecInfo := do
  let some info := env.find? decl | throw (IO.userError s!"census refusal: no constant {decl}")
  let some value := info.value? (allowOpaque := true) | return {}
  let value := value.consumeMData
  if value.isAppOfArity ``Lean.ParserDescr.node 3 then
    return { prec := some (← evalPrec env value.getAppArgs[1]!) }
  else if value.isAppOfArity ``Lean.ParserDescr.trailingNode 4 then
    let args := value.getAppArgs
    return { prec := some (← evalPrec env args[1]!), lhsPrec := some (← evalPrec env args[2]!) }
  else
    return {}

def renderOpt : Option Nat → String
  | some n => toString n
  | none => "-"

def firstRepr : Lean.Parser.FirstTokens → String
  | .epsilon => "epsilon"
  | .unknown => "unknown"
  | .tokens _ => "tokens"
  | .optTokens _ => "opt-tokens"

def behaviorRepr : Lean.Parser.LeadingIdentBehavior → String
  | .default => "default"
  | .symbol => "symbol"
  | .both => "both"

/-! ## Module helpers -/

def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => .anonymous

def inScope (m : Name) : Bool := m.getRoot == `Init || m.getRoot == `Std

/-- The modules whose global parser-extension token entries a file importing `roots` sees:
the reflexive-transitive closure of the imports recorded in the module headers. -/
partial def closure (env : Environment) (roots : Array Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots.toList
  while !todo.isEmpty do
    match todo with
    | [] => pure ()
    | m :: rest =>
      todo := rest
      if seen.contains m then continue
      seen := seen.insert m
      if let some idx := env.getModuleIdx? m then
        for imp in env.header.moduleData[idx.toNat]!.imports do
          todo := imp.module :: todo
  return seen

def globalTokens (env : Environment) (idx : Nat) : Array String := Id.run do
  let mut out := #[]
  for e in Lean.Parser.parserExtension.ext.getModuleEntries env idx do
    if let .global (.token tk) := e then out := out.push tk
  return out

/-! ## `grammar` mode -/

unsafe def grammar : IO UInt32 := do
  enableInitializersExecution
  let env ← importModules #[{module := `Init}, {module := `Std}, {module := `Lean}] {}
    (trustLevel := 1024) (loadExts := true)
  let opts : Options := {}
  let mut lines : Array String := #[]

  -- 1. every `_regBuiltin` declaration, classified
  let mut parsers : Array (Name × Name × Bool × Nat × Name) := #[] -- cat decl leading prio reg
  let mut keyed : Array (Name × Name × Name × Name) := #[]          -- attr key decl reg
  let mut families : Std.HashMap Name Nat := {}
  let mut regCount := 0
  for (name, info) in env.constants.map₁.toList do
    unless isRegBuiltin name do continue
    regCount := regCount + 1
    let some value := info.value? (allowOpaque := true)
      | throw (IO.userError s!"census refusal: {name} carries no value")
    match ← classify name value with
    | .parser cat decl leading prio =>
      parsers := parsers.push (cat, decl, leading, prio, name)
      families := families.insert `parser (families.getD `parser 0 + 1)
    | .keyed attr key decl =>
      keyed := keyed.push (attr, key, decl, name)
      families := families.insert attr (families.getD attr 0 + 1)
    | .other family =>
      families := families.insert family (families.getD family 0 + 1)

  -- 2. builtin parsers: tokens via the parser's own `ParserInfo`, precedence via its node
  let categories ← Lean.Parser.builtinParserCategoriesRef.get
  let mut tokenUnion : Std.HashSet String := {}
  let mut introducers : Std.HashMap String Nat := {}
  let mut parserRows : Array String := #[]
  let mut byCategory : Std.HashMap Name NameSet := {}
  for (cat, decl, leading, prio, _) in parsers do
    let p ← IO.ofExcept <| env.evalConst Lean.Parser.Parser opts decl
    let tks := p.info.collectTokens []
    for tk in dedupSorted tks.toArray do
      tokenUnion := tokenUnion.insert tk
      introducers := introducers.insert tk (introducers.getD tk 0 + 1)
    let prec ← precOf env decl
    let position := if leading then "leading" else "trailing"
    parserRows := parserRows.push <|
      s!"builtin-parser\t{render cat}\t{render decl}\t{position}\tprio={prio}\tprec={renderOpt prec.prec}\t" ++
      s!"lhs-prec={renderOpt prec.lhsPrec}\tfirst={firstRepr p.info.firstTokens}\t" ++
      s!"module={render (moduleOf env decl)}\ttokens={← joinTokens tks}"
    byCategory := byCategory.insert cat ((byCategory.getD cat {}).insert decl)

  -- totality (a): the runtime categories hold exactly the `_regBuiltin` parser rows
  let mut categoryRows : Array String := #[]
  for (cat, c) in categories.toList do
    let runtime := c.kinds.toList.map (·.1) |>.toArray |>.map render |> sortStrings
    let derived := (byCategory.getD cat {}).toList.toArray.map render |> sortStrings
    if runtime != derived then
      IO.eprintln s!"census refusal: category {cat}: runtime registers {runtime.size} parsers, _regBuiltin rows give {derived.size}"
      return 3
    categoryRows := categoryRows.push
      s!"category\t{render cat}\t{render c.declName}\t{behaviorRepr c.behavior}\tparsers={runtime.size}"
  for (cat, _) in byCategory.toList do
    unless categories.contains cat do
      IO.eprintln s!"census refusal: _regBuiltin registers parsers in unknown category {cat}"
      return 3

  -- totality (b): the runtime builtin token table is exactly the union of collected tokens
  let builtinTable ← Lean.Parser.builtinTokenTable.get
  let builtinTokens := sortStrings builtinTable.values
  let derivedTokens := sortStrings tokenUnion.toArray
  if builtinTokens != derivedTokens then
    IO.eprintln s!"census refusal: runtime builtin token table has {builtinTokens.size} tokens, the parsers collect {derivedTokens.size}"
    return 3

  -- 3. keyed registrations, named by their builtin attribute
  let attrs ← attributeMapRef.get
  let mut attrNames : Std.HashMap Name Name := {}
  for (attrName, impl) in attrs.toList do
    if attrName.toString.startsWith "builtin_" then
      attrNames := attrNames.insert impl.ref attrName
  let mut keyedRows : Array String := #[]
  for (attr, key, decl, _) in keyed do
    let some attrName := attrNames.get? attr
      | throw (IO.userError s!"census refusal: no builtin attribute is backed by {attr}")
    keyedRows := keyedRows.push
      s!"registration\t{render attrName}\t{render key}\t{render decl}\tmodule={render (moduleOf env decl)}"
  let mut familyRows : Array String := #[]
  for (family, n) in families.toList do
    let label := match attrNames.get? family with
      | some attrName => s!"attribute:{attrName}"
      | none => if family == `parser then "builtin-parser" else s!"call:{family}"
    familyRows := familyRows.push s!"registration-family\t{label}\t{n}"

  -- 4. the module header's own tokens (`parseHeader` adds them for the header only)
  let headerTokens := Lean.Parser.Module.header.info.collectTokens []
  let headerOnly := (dedupSorted headerTokens.toArray).filter fun tk => (builtinTable.find? tk).isNone

  -- 5. builtin node kinds, the header parser's kinds, and the named special kinds
  -- (`identKind`, `fieldIdxKind`, `interpolatedStrKind`, …: constants of type
  -- `SyntaxNodeKind` whose value is a name literal; token-level parsers build these nodes
  -- without registering them)
  let kindSet ← Lean.Parser.builtinSyntaxNodeKindSetRef.get
  let kinds := sortStrings (kindSet.toList.map (render ·.1)).toArray
  let headerKinds := sortStrings ((Lean.Parser.Module.header.info.collectKinds {}).toList.map (render ·.1)).toArray
  let mut kindConstantRows : Array String := #[]
  for (name, info) in env.constants.map₁.toList do
    if let .const ``Lean.SyntaxNodeKind [] := info.type then
      if let some value := info.value? (allowOpaque := true) then
        if let some kind := exprName? value then
          kindConstantRows := kindConstantRows.push
            s!"syntax-node-kind-constant\t{render name}\t{render kind}"

  -- 6. Init/Std modules: imports, parser-extension entries, syntax declarations, macros
  let parserCategories := (Lean.Parser.parserExtension.getState env).categories
  let mut moduleRows : Array String := #[]
  let mut moduleTokenRows : Array String := #[]
  let mut moduleKindRows : Array String := #[]
  let mut syntaxRows : Array String := #[]
  let mut keyedModuleRows : Array String := #[]
  let mut categoryDeclRows : Array String := #[]
  let mut moduleCount := 0
  let mut tokenEntryCount := 0
  let mut kindEntryCount := 0
  let mut descrByModule : Std.HashMap Name (Array Name) := {}
  for (name, info) in env.constants.map₁.toList do
    match info.type with
    | .const ``Lean.ParserDescr _ | .const ``Lean.TrailingParserDescr _ =>
      let m := moduleOf env name
      if inScope m then
        descrByModule := descrByModule.insert m ((descrByModule.getD m #[]).push name)
    | _ => pure ()
  let keyedExts : List (String × Lean.ScopedEnvExtension KeyedDeclsAttribute.OLeanEntry
      (KeyedDeclsAttribute.AttributeEntry Macro) (KeyedDeclsAttribute.ExtensionState Macro)) :=
    [("macro", Lean.Elab.macroAttribute.ext)]
  for idx in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[idx]!
    unless inScope m do
      -- Outside Init/Std only the kinds and categories are recorded: Init/Std parse trees
      -- contain nodes built by Lean.* parsers (the Verso docstring grammar), and totality
      -- needs to know those kinds exist.
      let mut kinds : Std.HashMap String (Array String) := {}
      for e in Lean.Parser.parserExtension.ext.getModuleEntries env idx do
        let (scope, entry) := match e with
          | .global entry => ("global", entry)
          | .scoped ns entry => (s!"scoped:{render ns}", entry)
        match entry with
        | .kind k => kinds := kinds.insert scope ((kinds.getD scope #[]).push (render k))
        | .category cat decl b =>
          categoryDeclRows := categoryDeclRows.push
            s!"module-category\t{render m}\t{render cat}\t{render decl}\t{behaviorRepr b}\t{scope}"
        | _ => pure ()
      for (scope, ks) in kinds.toList do
        moduleKindRows := moduleKindRows.push
          s!"module-kinds\t{render m}\t{scope}\t{" ".intercalate (dedupSorted ks).toList}"
      continue
    moduleCount := moduleCount + 1
    let imports := env.header.moduleData[idx]!.imports.map (render ·.module) |> dedupSorted
    moduleRows := moduleRows.push s!"module\t{render m}\timports={" ".intercalate imports.toList}"
    let mut parserEntries : Std.HashMap Name (Name × Nat × String) := {}
    let mut tokensByScope : Std.HashMap String (Array String) := {}
    let mut kindsByScope : Std.HashMap String (Array String) := {}
    for e in Lean.Parser.parserExtension.ext.getModuleEntries env idx do
      let (scope, entry) := match e with
        | .global entry => ("global", entry)
        | .scoped ns entry => (s!"scoped:{render ns}", entry)
      match entry with
      | .token tk =>
        tokenEntryCount := tokenEntryCount + 1
        tokensByScope := tokensByScope.insert scope ((tokensByScope.getD scope #[]).push (← checkToken tk))
      | .kind k =>
        kindEntryCount := kindEntryCount + 1
        kindsByScope := kindsByScope.insert scope ((kindsByScope.getD scope #[]).push (render k))
      | .parser cat decl prio => parserEntries := parserEntries.insert decl (cat, prio, scope)
      | .category cat decl b =>
        categoryDeclRows := categoryDeclRows.push
          s!"module-category\t{render m}\t{render cat}\t{render decl}\t{behaviorRepr b}\t{scope}"
    for (scope, tks) in tokensByScope.toList do
      moduleTokenRows := moduleTokenRows.push
        s!"module-tokens\t{render m}\t{scope}\t{" ".intercalate (dedupSorted tks).toList}"
    for (scope, ks) in kindsByScope.toList do
      moduleKindRows := moduleKindRows.push
        s!"module-kinds\t{render m}\t{scope}\t{" ".intercalate (dedupSorted ks).toList}"
    for decl in descrByModule.getD m #[] do
      let (leading, p) ← (Lean.Parser.mkParserOfConstant parserCategories decl).run { env, opts }
      let (cat, prio, scope) := match parserEntries.get? decl with
        | some (cat, prio, scope) => (render cat, toString prio, scope)
        | none => ("-", "-", "-")
      let position := if cat == "-" then "abbrev" else if leading then "leading" else "trailing"
      let prec ← descrPrecOf env decl
      syntaxRows := syntaxRows.push <|
        s!"syntax-decl\t{render m}\t{render decl}\t{cat}\t{position}\tprio={prio}\t" ++
        s!"prec={renderOpt prec.prec}\tlhs-prec={renderOpt prec.lhsPrec}\t{scope}\t" ++
        s!"tokens={← joinTokens (p.info.collectTokens [])}"
    for (decl, _) in parserEntries.toList do
      unless (descrByModule.getD m #[]).contains decl do
        -- a `[term_parser]`-style attribute on a hand-written `Parser`, not a ParserDescr
        let (cat, prio, scope) := parserEntries.get! decl
        syntaxRows := syntaxRows.push
          s!"syntax-decl\t{render m}\t{render decl}\t{render cat}\tparser-attribute\tprio={prio}\tprec=?\tlhs-prec=?\t{scope}\ttokens=?"
    for (label, ext) in keyedExts do
      for e in ext.ext.getModuleEntries env idx do
        let (scope, entry) := match e with
          | .global entry => ("global", entry)
          | .scoped ns entry => (s!"scoped:{render ns}", entry)
        keyedModuleRows := keyedModuleRows.push
          s!"module-{label}\t{render m}\t{render entry.key}\t{render entry.declName}\t{scope}"

  -- totality (c): derived closure tables agree with the tables `importModules` builds
  let mut closureRows : Array String := #[]
  for sample in [`Init.Prelude, `Init.Core, `Init.Data.List.Basic, `Init, `Std.Data.HashMap, `Std] do
    let mut derived : Std.HashSet String := builtinTable.values.foldl (·.insert ·) {}
    for m in (closure env #[sample]).toList do
      if let some idx := env.getModuleIdx? m then
        for tk in globalTokens env idx.toNat do derived := derived.insert tk
    enableInitializersExecution
    let sampleEnv ← importModules #[{module := sample}] {} (trustLevel := 1024) (loadExts := true)
    let actual := sortStrings (Lean.Parser.getTokenTable sampleEnv).values
    let derivedSorted := sortStrings derived.toArray
    if actual != derivedSorted then
      IO.eprintln s!"census refusal: closure token table for {sample}: importModules {actual.size}, derived {derivedSorted.size}"
      return 3
    closureRows := closureRows.push s!"closure-check\t{render sample}\ttokens={actual.size}\tagrees"

  -- emit, every section sorted
  let summary := #[
    s!"count\tregistrations\t{regCount}",
    s!"count\tbuiltin-parsers\t{parsers.size}",
    s!"count\tkeyed-registrations\t{keyed.size}",
    s!"count\tbuiltin-tokens\t{builtinTokens.size}",
    s!"count\theader-only-tokens\t{headerOnly.size}",
    s!"count\tbuiltin-node-kinds\t{kinds.size}",
    s!"count\theader-node-kinds\t{headerKinds.size}",
    s!"count\tsyntax-node-kind-constants\t{kindConstantRows.size}",
    s!"count\tcategories\t{categoryRows.size}",
    s!"count\tinit-std-modules\t{moduleCount}",
    s!"count\tinit-std-syntax-decls\t{syntaxRows.size}",
    s!"count\tinit-std-token-entries\t{tokenEntryCount}",
    s!"count\tinit-std-kind-entries\t{kindEntryCount}",
    s!"count\tinit-std-module-macros\t{keyedModuleRows.size}"]
  lines := lines ++ summary
  lines := lines ++ sortStrings closureRows
  lines := lines ++ sortStrings familyRows
  lines := lines ++ sortStrings categoryRows
  lines := lines ++ sortStrings parserRows
  for tk in builtinTokens do
    lines := lines.push s!"builtin-token\t{← checkToken tk}\tintroducers={introducers.getD tk 0}"
  for tk in headerOnly do
    lines := lines.push s!"header-token\t{← checkToken tk}"
  lines := lines ++ sortStrings keyedRows
  lines := lines ++ kinds.map (s!"builtin-node-kind\t{·}")
  lines := lines ++ headerKinds.map (s!"header-node-kind\t{·}")
  lines := lines ++ sortStrings kindConstantRows
  lines := lines ++ sortStrings moduleRows
  lines := lines ++ sortStrings moduleTokenRows
  lines := lines ++ sortStrings moduleKindRows
  lines := lines ++ sortStrings categoryDeclRows
  lines := lines ++ sortStrings syntaxRows
  lines := lines ++ sortStrings keyedModuleRows
  for l in lines do IO.println l
  return 0

/-! ## `replay` mode -/

/-- The command kinds that extend the grammar or the macro table. -/
def syntaxCommandKinds : List Name :=
  [``Lean.Parser.Command.syntax, ``Lean.Parser.Command.syntaxAbbrev,
   ``Lean.Parser.Command.syntaxCat, ``Lean.Parser.Command.macro,
   ``Lean.Parser.Command.macro_rules, ``Lean.Parser.Command.notation,
   ``Lean.Parser.Command.mixfix, ``Lean.Parser.Command.elab,
   ``Lean.Parser.Command.elab_rules]

partial def collectKinds (stx : Syntax) (acc : NameSet) : NameSet :=
  match stx with
  | .node _ k args => args.foldl (fun a s => collectKinds s a) (acc.insert k)
  | .ident .. => acc.insert identKind
  | .missing => acc.insert `missing
  | .atom .. => acc

partial def syntaxCommands (stx : Syntax) (acc : Array Syntax) : Array Syntax :=
  match stx with
  | .node _ k args =>
    let acc := if syntaxCommandKinds.contains k then acc.push stx else acc
    args.foldl (fun a s => syntaxCommands s a) acc
  | _ => acc

unsafe def replayOne (path : String) (mod : Name) : IO (Array String) := do
  let input ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext input path
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let opts : Options := {}
  let (env, messages) ← processHeader header opts messages inputCtx
    (trustLevel := 1024) (mainModule := mod)
  let s ← IO.processCommands inputCtx parserState (Command.mkState env messages opts)
  let errors := s.commandState.messages.toList.filter (·.severity == .error) |>.length
  let mut kinds := collectKinds header.raw {}
  let mut syntaxCmds : Array String := #[]
  for c in s.commands do
    kinds := collectKinds c kinds
    for cmd in syntaxCommands c #[] do
      let line := match cmd.getPos? with
        | some pos => toString (inputCtx.fileMap.toPosition pos).line
        | none => "-"
      syntaxCmds := syntaxCmds.push s!"syntax-command\t{render mod}\t{line}\t{render cmd.getKind}"
  let kindList := sortStrings (kinds.toList.map render).toArray
  let rel := match path.splitOn "vendor/lean4-src/" with
    | [_, rest] => rest
    | _ => path
  let mut out := #[
    s!"file\t{render mod}\t{rel}\tcommands={s.commands.size}\terrors={errors}\tkinds={kindList.size}",
    s!"uses\t{render mod}\t{" ".intercalate kindList.toList}"]
  out := out ++ syntaxCmds.qsort (fun a b =>
    let la := (a.splitOn "\t")[2]!.toNat!
    let lb := (b.splitOn "\t")[2]!.toNat!
    la < lb || (la == lb && a < b))
  return out

/-- One file per process. Replaying several files in one process is NOT faithful: measured at
the pin, `Init.Core` replayed after `Init.Prelude` in the same process parses 561 commands with
526 errors, against 551 commands and 0 errors alone — state the first replay leaves behind
changes the second. So the driver starts a fresh oracle process for every file. -/
unsafe def replay (path : String) (mod : String) : IO UInt32 := do
  enableInitializersExecution
  try
    for l in ← replayOne path mod.toName do IO.println l
    return 0
  catch e =>
    IO.println s!"file\t{mod}\t{path}\tfault={(toString e).replace "\t" " " |>.replace "\n" " "}"
    return 3

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | ["grammar"] => grammar
  | ["replay", path, mod] => replay path mod
  | _ =>
    IO.eprintln "usage: gen_grammar_census.lean (grammar | replay <path> <module>)"
    return 2
