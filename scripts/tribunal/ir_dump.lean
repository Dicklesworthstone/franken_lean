/-
Tribunal oracle for bead `fln-ir-decoder-call-graph-sjzl`: print every IR
declaration stored in the given `.ir` files, one per line, in a canonical
spelling that names every field.

It is run by the stock pinned `lean` and nothing else:

    lean --run scripts/tribunal/ir_dump.lean PATH.ir [PATH.ir ...]

The file is read with the pin's own `readModuleData`, and each entry is read as
the pin's own `Lean.IR.Decl`, so the container and the object layout are both
interpreted by the Reference. FrankenLean's decoder renders the same spelling
from its own reading of the same bytes (`crates/fln-olean/tests/ir.rs`); any
difference is a decoder defect or a defect here, and either is a finding.

Output: `#file PATH`, then one line per declaration in stored order, then
`#end N` with the declaration count. Spelling:

  name     components joined by `.`; a string component is written raw when it
           is made of `[A-Za-z0-9_'!?]` only and is non-empty, otherwise `%`
           followed by the hex of its UTF-8 bytes; a numeric component is `#N`;
           the anonymous name is `[anonymous]`
  string   the hex of its UTF-8 bytes, in double quotes
  literal  `(num HEX)` or `(str "HEX")`

Nothing here is executed by FrankenLean (D8): this is an oracle and a fixture
generator.
-/
import Lean
open Lean IR

namespace IrDump

def hexDigit (n : Nat) : Char := Nat.digitChar n

def hexByte (b : UInt8) : String :=
  String.ofList [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

def hexString (s : String) : String :=
  s.toUTF8.foldl (fun acc b => acc ++ hexByte b) ""

def plainChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?'

def component (s : String) : String :=
  if !s.isEmpty && s.all (fun c => c.toNat < 128 && plainChar c) then s else "%" ++ hexString s

def name : Name → String
  | .anonymous => "[anonymous]"
  | .str .anonymous s => component s
  | .num .anonymous n => "#" ++ toString n
  | .str p s => name p ++ "." ++ component s
  | .num p n => name p ++ ".#" ++ toString n

def optionName : Option Name → String
  | none => "none"
  | some n => "(some " ++ name n ++ ")"

partial def ty : IRType → String
  | .float => "float"
  | .uint8 => "u8"
  | .uint16 => "u16"
  | .uint32 => "u32"
  | .uint64 => "u64"
  | .usize => "usize"
  | .erased => "erased"
  | .object => "obj"
  | .tobject => "tobj"
  | .float32 => "float32"
  | .struct n ts => "(struct " ++ optionName n ++ ts.foldl (fun acc t => acc ++ " " ++ ty t) "" ++ ")"
  | .union n ts => "(union " ++ name n ++ ts.foldl (fun acc t => acc ++ " " ++ ty t) "" ++ ")"
  | .tagged => "tagged"
  | .void => "void"

def var (x : VarId) : String := "x" ++ toString x.idx
def join (j : JoinPointId) : String := "j" ++ toString j.idx
def flag (b : Bool) : String := if b then "1" else "0"

def arg : Arg → String
  | .var x => var x
  | .erased => "erased"

def args (ys : Array Arg) : String :=
  ys.foldl (fun acc y => acc ++ " " ++ arg y) ""

def ctorInfo (i : CtorInfo) : String :=
  "(ci " ++ name i.name ++ " " ++ toString i.cidx ++ " " ++ toString i.size ++ " "
    ++ toString i.usize ++ " " ++ toString i.ssize ++ ")"

def expr : IR.Expr → String
  | .ctor i ys => "(ctor " ++ ctorInfo i ++ args ys ++ ")"
  | .reset n x => "(reset " ++ toString n ++ " " ++ var x ++ ")"
  | .reuse x i u ys => "(reuse " ++ var x ++ " " ++ ctorInfo i ++ " " ++ flag u ++ args ys ++ ")"
  | .proj i x => "(proj " ++ toString i ++ " " ++ var x ++ ")"
  | .uproj i x => "(uproj " ++ toString i ++ " " ++ var x ++ ")"
  | .sproj n o x => "(sproj " ++ toString n ++ " " ++ toString o ++ " " ++ var x ++ ")"
  | .fap c ys => "(fap " ++ name c ++ args ys ++ ")"
  | .pap c ys => "(pap " ++ name c ++ args ys ++ ")"
  | .ap x ys => "(ap " ++ var x ++ args ys ++ ")"
  | .box t x => "(box " ++ ty t ++ " " ++ var x ++ ")"
  | .unbox x => "(unbox " ++ var x ++ ")"
  | .lit (.num v) => "(num " ++ String.ofList (Nat.toDigits 16 v) ++ ")"
  | .lit (.str v) => "(str \"" ++ hexString v ++ "\")"
  | .isShared x => "(isShared " ++ var x ++ ")"

def param (p : Param) : String :=
  "(p " ++ var p.x ++ " " ++ (if p.borrow then "b" else "o") ++ " " ++ ty p.ty ++ ")"

def params (ps : Array Param) : String :=
  "(" ++ (ps.foldl (fun (acc : String × Bool) p =>
    ((if acc.2 then acc.1 else acc.1 ++ " ") ++ param p, false)) ("", true)).1 ++ ")"

/-- The chain of instructions is walked in the accumulator, so a long body costs
no stack; only join-point values and `case` arms recurse. -/
partial def body (b : FnBody) (acc : String := "(body") : String :=
  match b with
  | .vdecl x t e b => body b (acc ++ " (vdecl " ++ var x ++ " " ++ ty t ++ " " ++ expr e ++ ")")
  | .jdecl j xs v b => body b (acc ++ " (jdecl " ++ join j ++ " " ++ params xs ++ " " ++ body v ++ ")")
  | .set x i y b => body b (acc ++ " (set " ++ var x ++ " " ++ toString i ++ " " ++ arg y ++ ")")
  | .setTag x c b => body b (acc ++ " (setTag " ++ var x ++ " " ++ toString c ++ ")")
  | .uset x i y b => body b (acc ++ " (uset " ++ var x ++ " " ++ toString i ++ " " ++ var y ++ ")")
  | .sset x i o y t b =>
    body b (acc ++ " (sset " ++ var x ++ " " ++ toString i ++ " " ++ toString o ++ " " ++ var y ++ " "
      ++ ty t ++ ")")
  | .inc x n c p b =>
    body b (acc ++ " (inc " ++ var x ++ " " ++ toString n ++ " " ++ flag c ++ " " ++ flag p ++ ")")
  | .dec x n c p b =>
    body b (acc ++ " (dec " ++ var x ++ " " ++ toString n ++ " " ++ flag c ++ " " ++ flag p ++ ")")
  | .del x b => body b (acc ++ " (del " ++ var x ++ ")")
  | .case tid x t cs =>
    acc ++ " (case " ++ name tid ++ " " ++ var x ++ " " ++ ty t
      ++ cs.foldl (fun r c => r ++ " " ++ match c with
        | .ctor i b => "(alt " ++ ctorInfo i ++ " " ++ body b ++ ")"
        | .default b => "(default " ++ body b ++ ")") ""
      ++ "))"
  | .ret x => acc ++ " (ret " ++ arg x ++ "))"
  | .jmp j ys => acc ++ " (jmp " ++ join j ++ args ys ++ "))"
  | .unreachable => acc ++ " (unreachable))"

def externEntry : ExternEntry → String
  | .adhoc b => "(adhoc " ++ name b ++ ")"
  | .inline b p => "(inline " ++ name b ++ " \"" ++ hexString p ++ "\")"
  | .standard b f => "(standard " ++ name b ++ " \"" ++ hexString f ++ "\")"
  | .opaque => "(opaque)"

def decl : Decl → String
  | .fdecl f xs t b info =>
    "(fdecl " ++ name f ++ " " ++ params xs ++ " " ++ ty t ++ " " ++ body b ++ " "
      ++ optionName info.sorryDep? ++ ")"
  | .extern f xs t ext =>
    "(extern " ++ name f ++ " " ++ params xs ++ " " ++ ty t ++ " ("
      ++ " ".intercalate (ext.entries.map externEntry) ++ "))"

end IrDump

unsafe def dumpFile (path : String) : IO Unit := do
  let (data, _region) ← readModuleData path
  IO.println ("#file " ++ path)
  let mut count := 0
  for (extension, entries) in data.entries do
    if extension == declMapExt.name then
      for entry in entries do
        let d : Decl := unsafeCast entry
        IO.println (IrDump.decl d)
        count := count + 1
  IO.println ("#end " ++ toString count)

unsafe def main (paths : List String) : IO UInt32 := do
  for path in paths do
    dumpFile path
  return 0
