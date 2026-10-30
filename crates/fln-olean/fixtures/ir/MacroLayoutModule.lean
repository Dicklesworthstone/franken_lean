prelude
import Init

set_option trace.compiler.ir.result true

namespace FrankenLean.MacroLayout

def sourceOriginal (leading : Substring.Raw) (pos : Nat)
    (trailing : Substring.Raw) (endPos : Nat) : Lean.SourceInfo :=
  .original leading ⟨pos⟩ trailing ⟨endPos⟩

def sourceSynthetic (pos endPos : Nat) (canonical : Bool) : Lean.SourceInfo :=
  .synthetic ⟨pos⟩ ⟨endPos⟩ canonical

def sourceNone (_ : Unit) : Lean.SourceInfo := .none

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

@[noinline] def nameMkStr1 (value : String) : Lean.Name := Lean.Name.mkStr1 value

@[noinline] def syntaxIsOfKind (value : Lean.Syntax) (kind : @& Lean.Name) : Bool :=
  value.isOfKind kind

@[noinline] def syntaxGetArg (value : @& Lean.Syntax) (index : @& Nat) : Lean.Syntax :=
  value.getArg index

@[noinline] def syntaxGetNumArgs (value : @& Lean.Syntax) : Nat := value.getNumArgs

end FrankenLean.MacroLayout
