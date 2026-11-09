prelude
import Init
import Lean.Syntax

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

@[noinline] def syntaxGetKind (value : Lean.Syntax) : Lean.Name := value.getKind

@[noinline] def syntaxSetKind (value : Lean.Syntax) (kind : Lean.Name) : Lean.Syntax :=
  value.setKind kind

@[noinline] def syntaxGetArgs (value : Lean.Syntax) : Array Lean.Syntax := value.getArgs

@[noinline] def syntaxSetArgs (value : Lean.Syntax) (args : Array Lean.Syntax) : Lean.Syntax :=
  value.setArgs args

@[noinline] def syntaxSetArg (value : Lean.Syntax) (index : Nat) (arg : Lean.Syntax) : Lean.Syntax :=
  value.setArg index arg

@[noinline] def syntaxIsAtom (value : Lean.Syntax) : Bool := value.isAtom

@[noinline] def syntaxGetAtomVal (value : Lean.Syntax) : String := value.getAtomVal

@[noinline] def syntaxSetAtomVal (value : Lean.Syntax) (text : String) : Lean.Syntax :=
  value.setAtomVal text

@[noinline] def syntaxGetHeadInfo (value : Lean.Syntax) : Lean.SourceInfo := value.getHeadInfo

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
