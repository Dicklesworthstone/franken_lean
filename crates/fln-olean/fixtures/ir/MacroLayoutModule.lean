prelude
import Init
import Lean.Syntax
import Lean.Expr

set_option trace.compiler.ir.result true

namespace FrankenLean.MacroLayout

def sourceOriginal (leading : Substring.Raw) (pos : Nat)
    (trailing : Substring.Raw) (endPos : Nat) : Lean.SourceInfo :=
  .original leading ⟨pos⟩ trailing ⟨endPos⟩

def sourceSynthetic (pos endPos : Nat) (canonical : Bool) : Lean.SourceInfo :=
  .synthetic ⟨pos⟩ ⟨endPos⟩ canonical

def sourceNone (_ : Unit) : Lean.SourceInfo := .none

@[noinline] def sourceOriginalPos (value : @& Lean.SourceInfo) : Nat :=
  match value with
  | .original _ pos _ _ => pos.byteIdx
  | _ => 0

@[noinline] def sourceOriginalTailPos (value : @& Lean.SourceInfo) : Nat :=
  match value with
  | .original _ _ _ endPos => endPos.byteIdx
  | _ => 0

@[noinline] def sourceOriginalLeading (value : @& Lean.SourceInfo) : Substring.Raw :=
  match value with
  | .original leading _ _ _ => leading
  | _ => "".toRawSubstring

@[noinline] def sourceOriginalTrailing (value : @& Lean.SourceInfo) : Substring.Raw :=
  match value with
  | .original _ _ trailing _ => trailing
  | _ => "".toRawSubstring

@[noinline] def sourceSyntheticPos (value : @& Lean.SourceInfo) : Nat :=
  match value with
  | .synthetic pos _ _ => pos.byteIdx
  | _ => 0

@[noinline] def sourceSyntheticTailPos (value : @& Lean.SourceInfo) : Nat :=
  match value with
  | .synthetic _ endPos _ => endPos.byteIdx
  | _ => 0

@[noinline] def sourceSyntheticCanonical (value : @& Lean.SourceInfo) : Bool :=
  match value with
  | .synthetic _ _ canonical => canonical
  | _ => false

def syntaxMissing (_ : Unit) : Lean.Syntax := .missing

def syntaxNode (info : Lean.SourceInfo) (kind : Lean.Name)
    (args : Array Lean.Syntax) : Lean.Syntax := .node info kind args

def syntaxAtom (info : Lean.SourceInfo) (value : String) : Lean.Syntax := .atom info value

def syntaxIdent (info : Lean.SourceInfo) (raw : Substring.Raw) (value : Lean.Name)
    (preresolved : List Lean.Syntax.Preresolved) : Lean.Syntax :=
  .ident info raw value preresolved

def syntaxRange (start stop : String.Pos.Raw) : Lean.Syntax.Range := ⟨start, stop⟩

@[noinline] def syntaxRangeStart (value : @& Lean.Syntax.Range) : String.Pos.Raw := value.start

@[noinline] def syntaxRangeStop (value : @& Lean.Syntax.Range) : String.Pos.Raw := value.stop

def substringRaw (value : String) (start stop : Nat) : Substring.Raw :=
  ⟨value, ⟨start⟩, ⟨stop⟩⟩

def preresolvedNamespace (name : Lean.Name) : Lean.Syntax.Preresolved := .namespace name

def preresolvedDecl (name : Lean.Name) (fields : List String) : Lean.Syntax.Preresolved :=
  .decl name fields

def macroContext (methods : Lean.Macro.MethodsRef) (quotContext : Lean.Name)
    (scope depth maxDepth : Nat) (ref : Lean.Syntax) : Lean.Macro.Context :=
  ⟨methods, quotContext, scope, depth, maxDepth, ref⟩

@[noinline] def contextMethods (value : @& Lean.Macro.Context) : Lean.Macro.MethodsRef :=
  value.methods

@[noinline] def contextQuotation (value : @& Lean.Macro.Context) : Lean.Name :=
  value.quotContext

@[noinline] def contextScope (value : @& Lean.Macro.Context) : Nat :=
  value.currMacroScope

@[noinline] def contextDepth (value : @& Lean.Macro.Context) : Nat :=
  value.currRecDepth

@[noinline] def contextMaxDepth (value : @& Lean.Macro.Context) : Nat :=
  value.maxRecDepth

@[noinline] def contextRef (value : @& Lean.Macro.Context) : Lean.Syntax :=
  value.ref

-- The constructor is private. The public inline operation exposes its exact
-- compiled layout without reaching through that source-level visibility.
def macroState : Lean.MacroM Nat := Lean.Macro.withFreshMacroScope (pure 5)

def resultOk (value : Lean.Syntax) (state : Lean.Macro.State) :
    EStateM.Result Lean.Macro.Exception Lean.Macro.State Lean.Syntax := .ok value state

def resultError (error : Lean.Macro.Exception) (state : Lean.Macro.State) :
    EStateM.Result Lean.Macro.Exception Lean.Macro.State Lean.Syntax := .error error state

def exceptionError (ref : Lean.Syntax) (message : String) : Lean.Macro.Exception :=
  .error ref message

def exceptionUnsupported (_ : Unit) : Lean.Macro.Exception := .unsupportedSyntax

def listCons (value : Lean.Syntax) (tail : List Lean.Syntax) : List Lean.Syntax := value :: tail

def listNil (_ : Unit) : List Lean.Syntax := []

def prod (name : Lean.Name) (value : String) : Lean.Name × String := (name, value)

def optionSome (value : Lean.Syntax) : Option Lean.Syntax := some value

def optionNone (_ : Unit) : Option Lean.Syntax := none

@[noinline] def nameMkStr1 (value : String) : Lean.Name := Lean.Name.mkStr1 value

@[noinline] def nameStr (parent : Lean.Name) (value : String) : Lean.Name :=
  .str parent value

@[noinline] def nameNum (parent : Lean.Name) (value : Nat) : Lean.Name :=
  .num parent value

@[noinline] def levelSucc (value : Lean.Level) : Lean.Level := .succ value
@[noinline] def levelMax (left right : Lean.Level) : Lean.Level := .max left right
@[noinline] def levelIMax (left right : Lean.Level) : Lean.Level := .imax left right
@[noinline] def levelParam (name : Lean.Name) : Lean.Level := .param name
@[noinline] def levelMVar (id : Lean.LMVarId) : Lean.Level := .mvar id

@[noinline] def exprBVar (index : Nat) : Lean.Expr := .bvar index
@[noinline] def exprFVar (id : Lean.FVarId) : Lean.Expr := .fvar id
@[noinline] def exprMVar (id : Lean.MVarId) : Lean.Expr := .mvar id
@[noinline] def exprSort (level : Lean.Level) : Lean.Expr := .sort level
@[noinline] def exprConst (name : Lean.Name) (levels : List Lean.Level) : Lean.Expr :=
  .const name levels
@[noinline] def exprApp (fn arg : Lean.Expr) : Lean.Expr := .app fn arg
@[noinline] def exprLam (name : Lean.Name) (type body : Lean.Expr)
    (info : Lean.BinderInfo) : Lean.Expr := .lam name type body info
@[noinline] def exprForall (name : Lean.Name) (type body : Lean.Expr)
    (info : Lean.BinderInfo) : Lean.Expr := .forallE name type body info
@[noinline] def exprLet (name : Lean.Name) (type value body : Lean.Expr)
    (nondep : Bool) : Lean.Expr := .letE name type value body nondep
@[noinline] def exprLit (value : Lean.Literal) : Lean.Expr := .lit value
@[noinline] def exprMData (data : Lean.MData) (value : Lean.Expr) : Lean.Expr :=
  .mdata data value
@[noinline] def exprProj (name : Lean.Name) (index : Nat) (value : Lean.Expr) : Lean.Expr :=
  .proj name index value

@[noinline] def nameHasMacroScopes (value : Lean.Name) : Bool := value.hasMacroScopes

@[noinline] def nameEraseMacroScopes (value : Lean.Name) : Lean.Name := value.eraseMacroScopes

@[noinline] def addMacroScope (context value : Lean.Name) (scope : Nat) : Lean.Name :=
  Lean.addMacroScope context value scope

@[noinline] def macroAddMacroScope (value : Lean.Name) (context : @& Lean.Macro.Context)
    (state : Lean.Macro.State) :
    EStateM.Result Lean.Macro.Exception Lean.Macro.State Lean.Name :=
  Lean.Macro.addMacroScope value context state

@[noinline] def syntaxIsOfKind (value : Lean.Syntax) (kind : @& Lean.Name) : Bool :=
  value.isOfKind kind

@[noinline] def syntaxGetArg (value : @& Lean.Syntax) (index : @& Nat) : Lean.Syntax :=
  value.getArg index

@[noinline] def syntaxGetNumArgs (value : @& Lean.Syntax) : Nat := value.getNumArgs

@[noinline] def syntaxIsNodeOf (value : Lean.Syntax) (kind : Lean.SyntaxNodeKind)
    (size : Nat) : Bool := value.isNodeOf kind size

@[noinline] def syntaxMatchesNull (value : Lean.Syntax) (size : Nat) : Bool :=
  value.matchesNull size

@[noinline] def syntaxMatchesIdent (value : Lean.Syntax) (id : Lean.Name) : Bool :=
  value.matchesIdent id

@[noinline] def syntaxMatchesLit (value : Lean.Syntax) (kind : Lean.SyntaxNodeKind)
    (text : String) : Bool := value.matchesLit kind text

@[noinline] def syntaxGetOptional (value : Lean.Syntax) : Option Lean.Syntax :=
  value.getOptional?

@[noinline] def syntaxMkLit (kind : Lean.SyntaxNodeKind) (value : String)
    (info : Lean.SourceInfo) : Lean.Syntax :=
  (Lean.Syntax.mkLit kind value info).raw

@[noinline] def syntaxMkStrLit (value : String) (info : Lean.SourceInfo) : Lean.Syntax :=
  (Lean.Syntax.mkStrLit value info).raw

@[noinline] def syntaxIsLit (kind : @& Lean.SyntaxNodeKind) (value : @& Lean.Syntax) :
    Option String :=
  Lean.Syntax.isLit? kind value

@[noinline] def syntaxIsStrLit (value : @& Lean.Syntax) : Option String := value.isStrLit?

@[noinline] def tSyntaxGetString (value : @& Lean.StrLit) : String := value.getString

@[noinline] def syntaxMkCharLit (value : Char) (info : Lean.SourceInfo) : Lean.Syntax :=
  (Lean.Syntax.mkCharLit value info).raw

@[noinline] def syntaxIsCharLit (value : @& Lean.Syntax) : Option Char := value.isCharLit?

@[noinline] def tSyntaxGetChar (value : @& Lean.CharLit) : Char := value.getChar

@[noinline] def syntaxMkNumLit (value : String) (info : Lean.SourceInfo) : Lean.Syntax :=
  (Lean.Syntax.mkNumLit value info).raw

@[noinline] def syntaxMkNatLit (value : Nat) (info : Lean.SourceInfo) : Lean.Syntax :=
  (Lean.Syntax.mkNatLit value info).raw

@[noinline] def syntaxIsNatLit (value : @& Lean.Syntax) : Option Nat := value.isNatLit?

@[noinline] def tSyntaxGetNat (value : @& Lean.NumLit) : Nat := value.getNat

@[noinline] def natReprFast (value : Nat) : String := Nat.reprFast value

@[noinline] def syntaxGetKind (value : Lean.Syntax) : Lean.Name := value.getKind

@[noinline] def syntaxSetKind (value : Lean.Syntax) (kind : Lean.Name) : Lean.Syntax :=
  value.setKind kind

@[noinline] def syntaxGetArgs (value : Lean.Syntax) : Array Lean.Syntax := value.getArgs

@[noinline] def syntaxGetSepArgs (value : Lean.Syntax) : Array Lean.Syntax := value.getSepArgs

@[noinline] def mkSepArray (values : Array Lean.Syntax) (sep : Lean.Syntax) : Array Lean.Syntax :=
  Lean.mkSepArray values sep

@[noinline] def syntaxMkSep (values : Array Lean.Syntax) (sep : Lean.Syntax) : Lean.Syntax :=
  Lean.Syntax.mkSep values sep

@[noinline] def sepArrayGetElems (value : Lean.Syntax.SepArray ",") : Array Lean.Syntax :=
  value.getElems

@[noinline] def tSepArrayGetElems (value : Lean.Syntax.TSepArray `term ",") : Array (Lean.TSyntax `term) :=
  value.getElems

@[noinline] def sepArrayOfElems (sep : String) (values : Array Lean.Syntax) : Lean.Syntax.SepArray sep :=
  Lean.Syntax.SepArray.ofElems values

-- The pin erases this typed wrapper to SepArray.ofElems, not a second native
-- entry point. The extraction script verifies that forwarding relationship.
@[noinline] def tSepArrayOfElems (sep : String) (values : Array (Lean.TSyntax `term)) : Lean.Syntax.TSepArray `term sep :=
  Lean.Syntax.TSepArray.ofElems values

@[noinline] def tSepArrayPush (sep : String) (values : Lean.Syntax.TSepArray `term sep) (value : Lean.TSyntax `term) : Lean.Syntax.TSepArray `term sep :=
  values.push value

@[noinline] def syntaxSetArgs (value : Lean.Syntax) (args : Array Lean.Syntax) : Lean.Syntax :=
  value.setArgs args

@[noinline] def syntaxSetArg (value : Lean.Syntax) (index : Nat) (arg : Lean.Syntax) : Lean.Syntax :=
  value.setArg index arg

@[noinline] def syntaxIsAtom (value : Lean.Syntax) : Bool := value.isAtom

@[noinline] def syntaxGetAtomVal (value : Lean.Syntax) : String := value.getAtomVal

@[noinline] def syntaxSetAtomVal (value : Lean.Syntax) (text : String) : Lean.Syntax :=
  value.setAtomVal text

@[noinline] def syntaxGetHeadInfo (value : Lean.Syntax) : Lean.SourceInfo := value.getHeadInfo

@[noinline] def syntaxGetInfo (value : Lean.Syntax) : Option Lean.SourceInfo := value.getInfo?

@[noinline] def syntaxGetHeadInfoOptional (value : Lean.Syntax) : Option Lean.SourceInfo :=
  value.getHeadInfo?

@[noinline] def syntaxGetRange (value : Lean.Syntax) (canonicalOnly : Bool) :
    Option Lean.Syntax.Range := value.getRange? canonicalOnly

@[noinline] def syntaxHasMissing (value : Lean.Syntax) : Bool := value.hasMissing

@[noinline] def syntaxReprint (value : Lean.Syntax) : Option String := value.reprint

@[noinline] def sourceInfoGetPos (value : @& Lean.SourceInfo) (canonicalOnly : Bool) :
    Option String.Pos.Raw := value.getPos? canonicalOnly

@[noinline] def sourceInfoGetTailPos (value : @& Lean.SourceInfo) (canonicalOnly : Bool) :
    Option String.Pos.Raw := value.getTailPos? canonicalOnly

@[noinline] def syntaxGetPos (value : @& Lean.Syntax) (canonicalOnly : Bool) :
    Option String.Pos.Raw := value.getPos? canonicalOnly

@[noinline] def syntaxGetTailPos (value : @& Lean.Syntax) (canonicalOnly : Bool) :
    Option String.Pos.Raw := value.getTailPos? canonicalOnly

@[noinline] def sourceInfoFromRef (value : @& Lean.Syntax) (canonical : Bool) :
    Lean.SourceInfo := Lean.SourceInfo.fromRef value canonical

@[noinline] def mkAtom (text : String) : Lean.Syntax := Lean.mkAtom text

@[noinline] def mkAtomFrom (value : @& Lean.Syntax) (text : String) (canonical : Bool) :
    Lean.Syntax := Lean.mkAtomFrom value text canonical

@[noinline] def mkIdent (value : Lean.Name) : Lean.Syntax := Lean.mkIdent value

@[noinline] def mkIdentFrom (ref : @& Lean.Syntax) (value : Lean.Name) (canonical : Bool) :
    Lean.Syntax := Lean.mkIdentFrom ref value canonical

@[noinline] def mkCIdent (value : Lean.Name) : Lean.Syntax := Lean.mkCIdent value

@[noinline] def mkCIdentFrom (ref : @& Lean.Syntax) (value : Lean.Name) (canonical : Bool) :
    Lean.Syntax := Lean.mkCIdentFrom ref value canonical

@[noinline] def replaceRef (value old : Lean.Syntax) : Lean.Syntax :=
  Lean.replaceRef value old

@[noinline] def macroThrowError (message : String) (context : @& Lean.Macro.Context)
    (state : Lean.Macro.State) :
    EStateM.Result Lean.Macro.Exception Lean.Macro.State Lean.Syntax :=
  Lean.Macro.throwError message context state

@[noinline] def macroThrowErrorAt (value : @& Lean.Syntax) (message : String)
    (context : @& Lean.Macro.Context) (state : Lean.Macro.State) :
    EStateM.Result Lean.Macro.Exception Lean.Macro.State Lean.Syntax :=
  Lean.Macro.throwErrorAt value message context state

@[noinline] def macroThrowUnsupported (state : Lean.Macro.State) :
    EStateM.Result Lean.Macro.Exception Lean.Macro.State Lean.Syntax :=
  Lean.Macro.throwUnsupported ⟨default, .anonymous, 0, 0, 0, .missing⟩ state

@[noinline] def syntaxSetInfo (info : Lean.SourceInfo) (value : Lean.Syntax) : Lean.Syntax :=
  value.setInfo info

@[noinline] def syntaxIsMissing (value : @& Lean.Syntax) : Bool := value.isMissing

@[noinline] def syntaxIsIdent (value : @& Lean.Syntax) : Bool := value.isIdent

@[noinline] def syntaxGetId (value : Lean.Syntax) : Lean.Name := value.getId

@[noinline] def macroGetCurrNamespace (context : @& Lean.Macro.Context)
    (state : Lean.Macro.State) :
    EStateM.Result Lean.Macro.Exception Lean.Macro.State Lean.Name :=
  Lean.Macro.getCurrNamespace context state

@[noinline] def macroHasDecl (name : Lean.Name) (context : @& Lean.Macro.Context)
    (state : Lean.Macro.State) :
    EStateM.Result Lean.Macro.Exception Lean.Macro.State Bool :=
  Lean.Macro.hasDecl name context state

@[noinline] def macroResolveNamespace (name : Lean.Name) (context : @& Lean.Macro.Context)
    (state : Lean.Macro.State) :
    EStateM.Result Lean.Macro.Exception Lean.Macro.State (List Lean.Name) :=
  Lean.Macro.resolveNamespace name context state

@[noinline] def macroResolveGlobalName (name : Lean.Name) (context : @& Lean.Macro.Context)
    (state : Lean.Macro.State) :
    EStateM.Result Lean.Macro.Exception Lean.Macro.State (List (Lean.Name × List String)) :=
  Lean.Macro.resolveGlobalName name context state

@[noinline] def macroExpandMacro (stx : Lean.Syntax) (context : @& Lean.Macro.Context)
    (state : Lean.Macro.State) :
    EStateM.Result Lean.Macro.Exception Lean.Macro.State (Option Lean.Syntax) :=
  Lean.Macro.expandMacro? stx context state

end FrankenLean.MacroLayout
