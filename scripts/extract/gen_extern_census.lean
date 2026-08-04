/-
gen_extern_census.lean — exact extern and builtin-environment observations
(beads franken_lean-53v, fln-3tye; plan Appendix C; Rules D5/D8-2).

Run only by the pin-verifying shell publisher. The Reference participates as an
offline census mine, never as a runtime component. `extern` preserves the v1
projection consumed by existing Golem work. `observed` emits one row for every
constant in the imported `Lean` closure. `partition` applies the reviewed,
first-match rules in ci/BUILTIN_PARTITION_POLICY.txt to the same sorted key set.

Names use a structural encoding which distinguishes string and numeric
components. Signatures are bound by a domain-separated four-lane structural
Expr digest and an explicit forall telescope (binder name/kind/domain digest);
source module, declaration kind/safety, environment-native attribute facts,
extern/implemented-by entries, effect class, and result identity remain
separately inspectable. The raw and partition projections are deliberately
separate so their bijection is checked outside the oracle process.
-/
import Lean
open Lean

partial def nameKey : Name → String
  | .anonymous => "a"
  | .str parent component => s!"{nameKey parent}/s{String.quote component}"
  | .num parent component => s!"{nameKey parent}/n{component}"

def entryRepr : ExternEntry → String
  | .adhoc backend => s!"adhoc:{backend}"
  | .inline backend pattern => s!"inline:{backend}:{pattern}"
  | .standard backend fn => s!"standard:{backend}:{fn}"
  | .opaque => "opaque"

def kindRepr : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "defn"
  | .thmInfo _ => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

/-- Root namespace component of a name, or `<anonymous-root>` for single-component names. -/
def rootOf (n : Name) : String :=
  match n.getRoot with
  | .anonymous => "<anonymous-root>"
  | root => toString root

def moduleName (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.header.moduleNames[idx.toNat]!
  | none => Name.anonymous

def safetyRepr : ConstantInfo → String
  | .defnInfo value =>
      match value.safety with
      | .safe => "safe"
      | .unsafe => "unsafe"
      | .partial => "partial"
  | info => if info.isUnsafe then "unsafe" else "safe"

def binderInfoRepr : BinderInfo → String
  | .default => "explicit"
  | .implicit => "implicit"
  | .strictImplicit => "strict-implicit"
  | .instImplicit => "instance"

structure StructuralDigest where
  lane0 : UInt64
  lane1 : UInt64
  lane2 : UInt64
  lane3 : UInt64
  deriving Inhabited

def StructuralDigest.seed : StructuralDigest where
  lane0 := 0xcbf29ce484222325
  lane1 := 0x84222325cbf29ce4
  lane2 := 0x9e3779b97f4a7c15
  lane3 := 0xd6e8feb86659fd93

def StructuralDigest.addByte (digest : StructuralDigest) (byte : UInt8) :
    StructuralDigest where
  lane0 := mixHash digest.lane0 byte.toUInt64
  lane1 := mixHash digest.lane1 (mixHash 0x01 byte.toUInt64)
  lane2 := mixHash digest.lane2 (mixHash 0x02 byte.toUInt64)
  lane3 := mixHash digest.lane3 (mixHash 0x03 byte.toUInt64)

def StructuralDigest.addRaw (digest : StructuralDigest) (value : String) :
    StructuralDigest :=
  value.toUTF8.foldl StructuralDigest.addByte digest

def StructuralDigest.addField (digest : StructuralDigest) (value : String) :
    StructuralDigest :=
  let bytes := value.toUTF8
  (digest.addRaw s!"{bytes.size}:").addRaw value

def StructuralDigest.render (digest : StructuralDigest) : String :=
  s!"mix256:{digest.lane0}:{digest.lane1}:{digest.lane2}:{digest.lane3}"

def structuralDigest (tag : String) (fields : List String) : StructuralDigest :=
  fields.foldl StructuralDigest.addField (StructuralDigest.seed.addField tag)

partial def levelDigest : Level → StructuralDigest
  | .zero => structuralDigest "level.zero" []
  | .succ level => structuralDigest "level.succ" [levelDigest level |>.render]
  | .max left right =>
      structuralDigest "level.max" [levelDigest left |>.render, levelDigest right |>.render]
  | .imax left right =>
      structuralDigest "level.imax" [levelDigest left |>.render, levelDigest right |>.render]
  | .param name => structuralDigest "level.param" [nameKey name]
  | .mvar id => structuralDigest "level.mvar" [nameKey id.name]

partial def expressionDigest (expression : Expr) :
    StateM (Std.HashMap Expr StructuralDigest) StructuralDigest := do
  if let some digest := (← get)[expression]? then
    return digest
  let digest ← match expression with
    | .bvar index =>
        pure <| structuralDigest "expr.bvar" [toString index]
    | .fvar id =>
        pure <| structuralDigest "expr.fvar" [nameKey id.name]
    | .mvar id =>
        pure <| structuralDigest "expr.mvar" [nameKey id.name]
    | .sort level =>
        pure <| structuralDigest "expr.sort" [levelDigest level |>.render]
    | .const name levels =>
        pure <| structuralDigest "expr.const"
          (nameKey name :: levels.map (levelDigest · |>.render))
    | .app function argument =>
        let functionDigest ← expressionDigest function
        let argumentDigest ← expressionDigest argument
        pure <| structuralDigest "expr.app"
          [functionDigest.render, argumentDigest.render]
    | .lam name domain body binderInfo =>
        let domainDigest ← expressionDigest domain
        let bodyDigest ← expressionDigest body
        pure <| structuralDigest "expr.lam"
          [nameKey name, binderInfoRepr binderInfo, domainDigest.render, bodyDigest.render]
    | .forallE name domain body binderInfo =>
        let domainDigest ← expressionDigest domain
        let bodyDigest ← expressionDigest body
        pure <| structuralDigest "expr.forall"
          [nameKey name, binderInfoRepr binderInfo, domainDigest.render, bodyDigest.render]
    | .letE name type value body nondependent =>
        let typeDigest ← expressionDigest type
        let valueDigest ← expressionDigest value
        let bodyDigest ← expressionDigest body
        pure <| structuralDigest "expr.let"
          [nameKey name, typeDigest.render, valueDigest.render, bodyDigest.render, toString nondependent]
    | .lit (.natVal value) =>
        pure <| structuralDigest "expr.literal.nat" [toString value]
    | .lit (.strVal value) =>
        pure <| structuralDigest "expr.literal.string" [value]
    | .mdata _ body =>
        expressionDigest body
    | .proj typeName index value =>
        let valueDigest ← expressionDigest value
        pure <| structuralDigest "expr.projection"
          [nameKey typeName, toString index, valueDigest.render]
  modify fun cache => cache.insert expression digest
  return digest

partial def telescope (type : Expr)
    (binders : Array (Name × BinderInfo × Expr) := #[]) :
    Array (Name × BinderInfo × Expr) × Expr :=
  match type.consumeMData with
  | .forallE name domain body binderInfo =>
      telescope body (binders.push (name, binderInfo, domain))
  | result => (binders, result)

partial def containsConstWhere (expression : Expr) (predicate : Name → Bool) : Bool :=
  match expression with
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => false
  | .const name _ => predicate name
  | .app function argument =>
      containsConstWhere function predicate || containsConstWhere argument predicate
  | .lam _ domain body _ | .forallE _ domain body _ =>
      containsConstWhere domain predicate || containsConstWhere body predicate
  | .letE _ type value body _ =>
      containsConstWhere type predicate
        || containsConstWhere value predicate
        || containsConstWhere body predicate
  | .mdata _ body => containsConstWhere body predicate
  | .proj typeName _ value =>
      predicate typeName || containsConstWhere value predicate

def nameLastString? : Name → Option String
  | .str _ value => some value
  | _ => none

def effectClass (result : Expr) : String :=
  let hasExact (names : List Name) :=
    containsConstWhere result fun name => names.contains name
  let hasLeanMonad :=
    containsConstWhere result fun name =>
      name.getRoot == `Lean
        && (nameLastString? name).any fun component => component.endsWith "M"
  if hasExact [`IO, `EIO, `BaseIO] then
    "io"
  else if hasExact [`Task] then
    "task"
  else if hasExact [`ST, `EST] then
    "state"
  else if hasLeanMonad then
    "toolchain-monad"
  else if hasExact [`ReaderT, `StateT, `ExceptT, `EStateM] then
    "monad-transformer"
  else
    "pure"

def inlineFact (env : Environment) (name : Name) : String :=
  match Compiler.getInlineAttribute? env name with
  | none => "-"
  | some .inline => "inline"
  | some .noinline => "noinline"
  | some .macroInline => "macro_inline"
  | some .inlineIfReduce => "inline_if_reduce"
  | some .alwaysInline => "always_inline"

def environmentAttributeFacts
    (env : Environment)
    (name : Name)
    (externData? : Option ExternAttrData)
    (implementedBy? : Option Name) : String := Id.run do
  let mut facts : Array String := #[]
  if externData?.isSome then
    facts := facts.push "extern"
  if implementedBy?.isSome then
    facts := facts.push "implemented_by"
  if isMarkedMeta env name then
    facts := facts.push "meta"
  if isClass env name then
    facts := facts.push "class"
  if Meta.isInstanceCore env name then
    facts := facts.push "instance"
  if (getExportNameFor? env name).isSome then
    facts := facts.push "export"
  let inline := inlineFact env name
  if inline != "-" then
    facts := facts.push s!"inline={inline}"
  let reducibility := reprStr (getReducibilityStatusCore env name)
  facts := facts.push s!"reducibility={reducibility}"
  ";".intercalate facts.toList

def sortedNames (env : Environment) : Array (String × Name) :=
  let names := env.constants.toList.toArray.map fun (name, _) => (nameKey name, name)
  names.qsort fun left right => left.1 < right.1

def partition
    (env : Environment)
    (name : Name)
    (info : ConstantInfo)
    (externData? : Option ExternAttrData)
    (implementedBy? : Option Name)
    (effect : String) : String × String :=
  let kind := kindRepr info
  if externData?.isSome then
    ("toolchain-api", "extern-intrinsic")
  else if implementedBy?.isSome then
    ("toolchain-api", "implemented-by-intrinsic")
  else if kind == "induct" || kind == "ctor" || kind == "rec" || kind == "quot" then
    ("user-facing-data", "kernel-generated-data-surface")
  else if kind == "thm" then
    ("library-code", "proof-library-source")
  else if isMarkedMeta env name then
    ("toolchain-api", "meta-runtime")
  else if safetyRepr info == "unsafe" || safetyRepr info == "partial" then
    ("toolchain-api", "native-runtime-safety")
  else if effect != "pure" then
    ("toolchain-api", "effectful-runtime")
  else if (moduleName env name).getRoot == `Lean then
    ("toolchain-api", "lean-toolchain-namespace")
  else
    ("library-code", "pure-library-source")

def emitExtern (env : Environment) : IO Unit := do
  let mut externRows : Array (String × String) := #[]
  let mut summary : Std.TreeMap String Nat := {}
  let mut total := 0
  for (name, ci) in env.constants.toList do
    total := total + 1
    let kind := kindRepr ci
    let summaryKey := s!"{rootOf name}\t{kind}"
    summary := summary.insert summaryKey (summary.getD summaryKey 0 + 1)
    if let some data := Lean.externAttr.getParam? env name then
      let modName := match env.getModuleIdxFor? name with
        | some idx => toString env.header.moduleNames[idx.toNat]!
        | none => "<current>"
      let entries := ";".intercalate (data.entries.map entryRepr)
      let key := toString name
      externRows := externRows.push
        (key, s!"extern\t{key}\t{kind}\t{modName}\t{ci.type.getForallArity}\t{ci.levelParams.length}\t{entries}")
  let sorted := externRows.qsort (fun a b => a.1 < b.1)
  IO.println s!"extern_count\t{sorted.size}"
  IO.println s!"constant_count\t{total}"
  IO.println "columns\tname\tkind\tmodule\tarity\tlevel_params\tentries"
  for (_, row) in sorted do
    IO.println row
  IO.println "columns_summary\troot\tkind\tcount"
  for (key, count) in summary do
    IO.println s!"summary\t{key}\t{count}"

def emitObserved (env : Environment) : IO Unit := do
  let names := sortedNames env
  let modules := env.header.moduleNames.map nameKey
    |>.qsort fun left right => left < right
  let attributes := (getAttributeNames env).toArray.map nameKey
    |>.qsort fun left right => left < right
  let mut externCount := 0
  for (_, name) in names do
    let some info := env.find? name
      | throw <| IO.userError s!"environment changed during walk: {name}"
    if (externAttr.getParam? env name).isSome then
      externCount := externCount + 1
    if info.name != name then
      throw <| IO.userError s!"environment key/name disagreement: {name}"
  IO.println s!"constant_count\t{names.size}"
  IO.println s!"module_count\t{env.header.moduleNames.size}"
  IO.println s!"attribute_count\t{attributes.size}"
  IO.println s!"extern_count\t{externCount}"
  IO.println s!"attribute_registry\t{String.quote (",".intercalate attributes.toList)}"
  for h : index in [:modules.size] do
    IO.println s!"module_registry_{index}\t{String.quote modules[index]}"
  IO.println "columns\tkey\tdisplay-name\tkind\tmodule\tlevel-params\tarity\ttelescope\tsignature-root\tresult-root\tresult-head\tsafety\tattributes\textern-entries\timplemented-by\teffect"
  let mut digestCache : Std.HashMap Expr StructuralDigest := {}
  for (key, name) in names do
    let some info := env.find? name
      | throw <| IO.userError s!"environment changed during walk: {name}"
    let externData? := externAttr.getParam? env name
    let implementedBy? := Compiler.implementedByAttr.getParam? env name
    let (binders, result) := telescope info.type
    let (signatureDigest, nextCache) := (expressionDigest info.type).run digestCache
    digestCache := nextCache
    let (resultDigest, nextCache) := (expressionDigest result).run digestCache
    digestCache := nextCache
    let mut binderFields : Array String := #[]
    for (binderName, binderInfo, domain) in binders do
      let (domainDigest, nextCache) := (expressionDigest domain).run digestCache
      digestCache := nextCache
      binderFields := binderFields.push <|
        s!"{String.quote (nameKey binderName)}:{binderInfoRepr binderInfo}:{domainDigest.render}"
    let resultHead := match result.getAppFn.constName? with
      | some head => nameKey head
      | none => "-"
    let externEntries := match externData? with
      | some data => ";".intercalate (data.entries.map entryRepr)
      | none => "-"
    let implementedBy := implementedBy?.map nameKey |>.getD "-"
    let attributes :=
      environmentAttributeFacts env name externData? implementedBy?
    IO.println <|
      s!"observed\t{String.quote key}\t{toString name}\t{kindRepr info}\t{String.quote (nameKey (moduleName env name))}\t{String.quote (",".intercalate (info.levelParams.map nameKey))}\t{binders.size}\t{String.quote (";".intercalate binderFields.toList)}\t{signatureDigest.render}\t{resultDigest.render}\t{String.quote resultHead}\t{safetyRepr info}\t{String.quote attributes}\t{String.quote externEntries}\t{String.quote implementedBy}\t{effectClass result}"

def emitPartitions (env : Environment) : IO Unit := do
  let names := sortedNames env
  let mut toolchainApi := 0
  let mut libraryCode := 0
  let mut userFacingData := 0
  for (_, name) in names do
    let some info := env.find? name
      | throw <| IO.userError s!"environment changed during walk: {name}"
    let externData? := externAttr.getParam? env name
    let implementedBy? := Compiler.implementedByAttr.getParam? env name
    let (_, result) := telescope info.type
    let (partitionClass, _) :=
      partition env name info externData? implementedBy? (effectClass result)
    match partitionClass with
    | "toolchain-api" => toolchainApi := toolchainApi + 1
    | "library-code" => libraryCode := libraryCode + 1
    | "user-facing-data" => userFacingData := userFacingData + 1
    | _ => throw <| IO.userError s!"unclassified declaration: {name}"
  IO.println s!"constant_count\t{names.size}"
  IO.println s!"toolchain_api_count\t{toolchainApi}"
  IO.println s!"library_code_count\t{libraryCode}"
  IO.println s!"user_facing_data_count\t{userFacingData}"
  IO.println "unresolved_count\t0"
  IO.println "columns\tkey\tpartition\treason"
  for (key, name) in names do
    let some info := env.find? name
      | throw <| IO.userError s!"environment changed during walk: {name}"
    let externData? := externAttr.getParam? env name
    let implementedBy? := Compiler.implementedByAttr.getParam? env name
    let (_, result) := telescope info.type
    let (partitionClass, reason) :=
      partition env name info externData? implementedBy? (effectClass result)
    IO.println s!"partition\t{String.quote key}\t{partitionClass}\t{reason}"

def main (args : List String) : IO UInt32 := do
  let env ← importModules #[{module := `Lean}] {} (trustLevel := 1024)
  match args with
  | ["extern"] =>
      emitExtern env
      return 0
  | ["observed"] =>
      emitObserved env
      return 0
  | ["partition"] =>
      emitPartitions env
      return 0
  | _ =>
      IO.eprintln "usage: lean --run gen_extern_census.lean extern|observed|partition"
      return 2
