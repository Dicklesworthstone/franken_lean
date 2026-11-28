//! Native compilation, including actual Reference interpretation of the output.
#![forbid(unsafe_code)]

use fln::ir::{self, CompileLimits};
use fln::{Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, VmExit};
use fln_core::{name::Name, options::KVMap};
use fln_olean::ir::write::{IrWriteInput, IrWriteLimits, encode_ir};
use fln_olean::ir::{IrArg, IrBody, IrDecl, IrExpr, IrLit, IrNat, IrStmt, IrTerminal, IrType};
use fln_olean::region::{OleanView, WalkBudget};
use fln_olean::write::{ModuleWriteInput, OleanWriteHeader};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::{Path, PathBuf},
    process::Command,
};

const HELPERS: &str = "def keep (x : Nat) : Nat := x\ndef invoke (f : Nat -> Nat) (x : Nat) : Nat := f x\ndef invokeString (f : Nat -> String) (x : Nat) : String := f x\n";

// Closed exported signatures keep these native boxed layouts private. The two
// tag-zero shapes deliberately differ in size; no source-data ABI is promised.
const INTERNAL_DATA_HELPERS: &str = concat!(
    "structure IRTextPair where\n  left : String\n  right : String\n",
    "structure IRNested where\n  pair : IRTextPair\n",
    "structure IRFunctionBox where\n  run : Nat -> Nat\n",
    "structure IRBoolBox where\n  value : Bool\n",
);

const ENUM_DATA_HELPERS: &str = concat!(
    "inductive IRChoice where\n | north\n | east\n | west\n",
    "inductive IROther where\n | first\n | second\n | third\n | fourth\n",
    "inductive IRSingle where\n | only\n",
    "structure IREnumBox where\n first : IRChoice\n second : IRChoice\n",
    "inductive IRPayload where\n | empty\n | value (n : Nat)\n",
    "inductive IRScalarPayload where\n | empty\n | value (b : Bool)\n",
    "inductive IRParameterized (A : Type) where\n | first\n | second\n",
    "abbrev IRAlias := IRChoice\n",
);

struct EnumExportCase {
    ty: &'static str,
    body: &'static str,
    application: &'static str,
    expected: &'static str,
    parameters: Vec<IrType>,
    result: IrType,
    reduced: Option<(&'static str, &'static str)>,
}

fn enum_export_cases() -> Vec<EnumExportCase> {
    vec![
        EnumExportCase {
            ty: "IRChoice",
            body: "IRChoice.west",
            application: "match compiled with | .north => 0 | .east => 1 | .west => 2",
            expected: "2",
            parameters: vec![],
            result: IrType::UInt8,
            reduced: None,
        },
        EnumExportCase {
            ty: "IRChoice -> IRChoice",
            body: "fun c => c",
            application: "match compiled IRChoice.east with | .north => 0 | .east => 1 | .west => 2",
            expected: "1",
            parameters: vec![IrType::UInt8],
            result: IrType::UInt8,
            reduced: None,
        },
        EnumExportCase {
            ty: "IRChoice -> IRChoice",
            body: "fun c => match c with | .north => IRChoice.east | .east => IRChoice.west | .west => IRChoice.north",
            application: "((match compiled IRChoice.north with | .north => 0 | .east => 1 | .west => 2), (match compiled IRChoice.east with | .north => 0 | .east => 1 | .west => 2), (match compiled IRChoice.west with | .north => 0 | .east => 1 | .west => 2))",
            expected: "(1, 2, 0)",
            parameters: vec![IrType::UInt8],
            result: IrType::UInt8,
            reduced: None,
        },
        EnumExportCase {
            ty: "(IRChoice -> IRChoice) -> IRChoice -> IRChoice",
            body: "fun f c => f c",
            application: "match compiled (fun _ => IRChoice.west) IRChoice.north with | .north => 0 | .east => 1 | .west => 2",
            expected: "2",
            parameters: vec![IrType::Object, IrType::UInt8],
            result: IrType::UInt8,
            reduced: None,
        },
        EnumExportCase {
            ty: "IRSingle",
            body: "IRSingle.only",
            application: "match compiled with | .only => 7",
            expected: "7",
            parameters: vec![],
            result: IrType::Tagged,
            reduced: None,
        },
        EnumExportCase {
            ty: "IRSingle -> IRSingle",
            body: "fun x => x",
            application: "match compiled IRSingle.only with | .only => 7",
            expected: "7",
            parameters: vec![IrType::Tagged],
            result: IrType::Tagged,
            reduced: None,
        },
        EnumExportCase {
            ty: "IRSingle -> Nat -> Nat",
            body: "fun _ n => n",
            application: "compiled IRSingle.only 42",
            expected: "42",
            parameters: vec![IrType::Tagged, IrType::TObject],
            result: IrType::TObject,
            reduced: Some(("Nat -> Nat", "compiled 42")),
        },
        EnumExportCase {
            ty: "IRChoice -> Nat -> Nat",
            body: "fun _ n => n",
            application: "compiled IRChoice.west 42",
            expected: "42",
            parameters: vec![IrType::UInt8, IrType::TObject],
            result: IrType::TObject,
            reduced: Some(("Nat -> Nat", "compiled 42")),
        },
        EnumExportCase {
            ty: "IRChoice -> IRChoice",
            body: "fun c => let boxed := IREnumBox.mk IRChoice.east c; boxed.second",
            application: "match compiled IRChoice.west with | .north => 0 | .east => 1 | .west => 2",
            expected: "2",
            parameters: vec![IrType::UInt8],
            result: IrType::UInt8,
            reduced: None,
        },
        EnumExportCase {
            ty: "IRChoice -> IROther -> IRChoice",
            body: "fun c _ => c",
            application: "match compiled IRChoice.east IROther.fourth with | .north => 0 | .east => 1 | .west => 2",
            expected: "1",
            parameters: vec![IrType::UInt8, IrType::UInt8],
            result: IrType::UInt8,
            reduced: Some((
                "IRChoice -> IRChoice",
                "match compiled IRChoice.east with | .north => 0 | .east => 1 | .west => 2",
            )),
        },
        EnumExportCase {
            ty: "(IRChoice -> Nat) -> IRChoice -> Nat",
            body: "fun f c => f c",
            application: "compiled (fun c => match c with | .north => 11 | .east => 22 | .west => 33) IRChoice.west",
            expected: "33",
            parameters: vec![IrType::Object, IrType::UInt8],
            result: IrType::TObject,
            reduced: None,
        },
        EnumExportCase {
            ty: "(IRChoice -> Nat) -> Nat",
            body: "fun f => f IRChoice.west",
            application: "compiled (fun c => match c with | .north => 11 | .east => 22 | .west => 33)",
            expected: "33",
            parameters: vec![IrType::Object],
            result: IrType::TObject,
            reduced: None,
        },
    ]
}

fn enum_base() -> Engine {
    base()
        .check_source_files(
            &[ENUM_DATA_HELPERS.as_bytes()],
            &KVMap::new(),
            fln::SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

const BOXED_DATA_HELPERS: &str = concat!(
    "structure IRBoxedRecord where\n number : Nat\n text : String\n",
    "structure IRReverseRecord where\n text : String\n number : Nat\n",
    "structure IRWideRecord where\n number : Nat\n text : String\n extra : Nat\n",
    "inductive IRBoxedSum where\n | empty\n | number (n : Nat)\n | text (s : String)\n | pair (n : Nat) (s : String)\n",
    "inductive IRPayloadFirst where\n | value (n : Nat) (s : String)\n | empty\n",
    "structure IRNatWrapper where\n value : Nat\n",
    "structure IRStringWrapper where\n value : String\n",
    "structure IRScalarBox where\n number : Nat\n flag : Bool\n",
    "structure IRInterleaved where\n first : Bool\n number : Nat\n second : Bool\n text : String\n",
    "structure IRScalarReordered where\n number : Nat\n first : Bool\n text : String\n second : Bool\n",
    "structure IRAllBools where\n first : Bool\n second : Bool\n third : Bool\n",
    "structure IRProofBox where\n number : Nat\n proof : True\n",
    "inductive IRRecursive where\n | empty\n | next (n : Nat) (tail : IRRecursive)\n",
    "inductive IRRecursiveFirst where\n | next (n : Nat) (tail : IRRecursiveFirst)\n | empty\n",
    "inductive IRRecursiveTree where\n | leaf (n : Nat) (text : String)\n | node (left : IRRecursiveTree) (flag : Bool) (right : IRRecursiveTree)\n",
    "inductive IRRecursiveLoop where\n | next (tail : IRRecursiveLoop)\n",
    "inductive IRBoxedParam (A : Type) where\n | mk (value : A) (n : Nat)\n",
    "abbrev IRBoxedAlias := IRBoxedRecord\n",
);

struct BoxedExportCase {
    ty: &'static str,
    body: &'static str,
    application: &'static str,
    expected: &'static str,
    parameters: Vec<IrType>,
    result: IrType,
    reduced: Option<(&'static str, &'static str)>,
}

fn boxed_export_cases() -> Vec<BoxedExportCase> {
    vec![
        BoxedExportCase {
            ty: "IRBoxedRecord",
            body: "IRBoxedRecord.mk 42 \"constant payload\"",
            application: "(compiled.number, compiled.text)",
            expected: "(42, \"constant payload\")",
            parameters: vec![],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRBoxedRecord -> IRBoxedRecord",
            body: "fun p => p",
            application: "let p := IRBoxedRecord.mk large heap; let q := compiled p; (q.number, q.text, p.number, p.text)",
            expected: "(184467440737095516160, \"boxed heap payload\", 184467440737095516160, \"boxed heap payload\")",
            parameters: vec![IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRBoxedRecord -> String",
            body: "fun p => p.text",
            application: "let p := IRBoxedRecord.mk large heap; (compiled p, p.text, p.number)",
            expected: "(\"boxed heap payload\", \"boxed heap payload\", 184467440737095516160)",
            parameters: vec![IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRReverseRecord -> Nat",
            body: "fun p => p.number",
            application: "let p := IRReverseRecord.mk heap large; (compiled p, p.text)",
            expected: "(184467440737095516160, \"boxed heap payload\")",
            parameters: vec![IrType::Object],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "Nat -> String -> IRBoxedRecord",
            body: "fun n s => IRBoxedRecord.mk n s",
            application: "let p := compiled large heap; (p.number, p.text, heap)",
            expected: "(184467440737095516160, \"boxed heap payload\", \"boxed heap payload\")",
            parameters: vec![IrType::TObject, IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "(IRBoxedRecord -> IRBoxedRecord) -> IRBoxedRecord -> IRBoxedRecord",
            body: "fun f p => f p",
            application: "let p := IRBoxedRecord.mk large heap; let q := compiled (fun x => IRBoxedRecord.mk (x.number + 1) (x.text ++ \"!\")) p; (q.number, q.text, p.number, p.text)",
            expected: "(184467440737095516161, \"boxed heap payload!\", 184467440737095516160, \"boxed heap payload\")",
            parameters: vec![IrType::Object, IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "(IRBoxedRecord -> String) -> String",
            body: "fun f => f (IRBoxedRecord.mk 42 \"inside\")",
            application: "compiled (fun p => p.text ++ heap)",
            expected: "\"insideboxed heap payload\"",
            parameters: vec![IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRBoxedRecord -> Nat -> Nat",
            body: "fun _ n => n",
            application: "compiled (IRBoxedRecord.mk large heap) 42",
            expected: "42",
            parameters: vec![IrType::Object, IrType::TObject],
            result: IrType::TObject,
            reduced: Some(("Nat -> Nat", "compiled 42")),
        },
        BoxedExportCase {
            ty: "IRPayloadFirst -> Nat -> Nat",
            body: "fun _ n => n",
            application: "compiled IRPayloadFirst.empty 42",
            expected: "42",
            parameters: vec![IrType::TObject, IrType::TObject],
            result: IrType::TObject,
            reduced: Some(("Nat -> Nat", "compiled 42")),
        },
        BoxedExportCase {
            ty: "IRBoxedSum",
            body: "IRBoxedSum.empty",
            application: "match compiled with | .empty => 0 | _ => 1",
            expected: "0",
            parameters: vec![],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRBoxedSum -> IRBoxedSum",
            body: "fun value => value",
            application: "let p := IRBoxedSum.text heap; ((match compiled p with | .text s => s | _ => \"wrong\"), (match compiled .empty with | .empty => 0 | _ => 1), (match p with | .text s => s | _ => \"lost\"))",
            expected: "(\"boxed heap payload\", 0, \"boxed heap payload\")",
            parameters: vec![IrType::TObject],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRBoxedSum -> String",
            body: "fun value => match value with | .empty => \"empty\" | .number _ => \"number\" | .text s => s | .pair _ s => s",
            application: "(compiled .empty, compiled (.number large), compiled (.text heap), compiled (.pair large heap))",
            expected: "(\"empty\", \"number\", \"boxed heap payload\", \"boxed heap payload\")",
            parameters: vec![IrType::TObject],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "Nat -> String -> IRBoxedSum",
            body: "fun n s => IRBoxedSum.pair n s",
            application: "match compiled large heap with | .pair n s => (n, s, heap) | _ => (0, \"wrong\", heap)",
            expected: "(184467440737095516160, \"boxed heap payload\", \"boxed heap payload\")",
            parameters: vec![IrType::TObject, IrType::Object],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRBoxedRecord -> IRReverseRecord -> IRBoxedRecord",
            body: "fun p _ => p",
            application: "let p := compiled (IRBoxedRecord.mk large heap) (IRReverseRecord.mk heap large); (p.number, p.text)",
            expected: "(184467440737095516160, \"boxed heap payload\")",
            parameters: vec![IrType::Object, IrType::Object],
            result: IrType::Object,
            reduced: Some((
                "IRBoxedRecord -> IRBoxedRecord",
                "let p := compiled (IRBoxedRecord.mk large heap); (p.number, p.text)",
            )),
        },
        BoxedExportCase {
            ty: "IRPayload -> IRPayload",
            body: "fun x => x",
            application: "match compiled (IRPayload.value large) with | .empty => 0 | .value n => n",
            expected: "184467440737095516160",
            parameters: vec![IrType::TObject],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "(IRPayload -> Nat) -> Nat",
            body: "fun f => f IRPayload.empty",
            application: "compiled (fun x => match x with | .empty => 42 | .value n => n)",
            expected: "42",
            parameters: vec![IrType::Object],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRTextPair -> String",
            body: "fun p => p.right",
            application: "compiled (IRTextPair.mk \"left\" heap)",
            expected: "\"boxed heap payload\"",
            parameters: vec![IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "String -> IRTextPair",
            body: "fun s => IRTextPair.mk s s",
            application: "let p := compiled heap; (p.left, p.right, heap)",
            expected: "(\"boxed heap payload\", \"boxed heap payload\", \"boxed heap payload\")",
            parameters: vec![IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "(IRTextPair -> String) -> String",
            body: "fun f => f (IRTextPair.mk \"a\" \"b\")",
            application: "compiled (fun p => p.left ++ p.right)",
            expected: "\"ab\"",
            parameters: vec![IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "(IRReverseRecord -> IRBoxedRecord) -> IRReverseRecord -> IRBoxedRecord",
            body: "fun f p => f p",
            application: "let p := IRReverseRecord.mk heap large; let q := compiled (fun x => IRBoxedRecord.mk (x.number + 1) (x.text ++ \"!\")) p; (q.number, q.text, p.text, p.number)",
            expected: "(184467440737095516161, \"boxed heap payload!\", \"boxed heap payload\", 184467440737095516160)",
            parameters: vec![IrType::Object, IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRBoxedRecord -> IRBoxedRecord",
            body: "fun p => let box := IRFunctionBox.mk (fun _ => p.number); IRBoxedRecord.mk (box.run 7) p.text",
            application: "let p := compiled (IRBoxedRecord.mk large heap); (p.number, p.text)",
            expected: "(184467440737095516160, \"boxed heap payload\")",
            parameters: vec![IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRScalarBox",
            body: "IRScalarBox.mk 42 true",
            application: "(compiled.number, compiled.flag)",
            expected: "(42, true)",
            parameters: vec![],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRScalarBox -> IRScalarBox",
            body: "fun p => p",
            application: "let p := IRScalarBox.mk large true; let q := compiled p; (q.number, q.flag, p.number, p.flag)",
            expected: "(184467440737095516160, true, 184467440737095516160, true)",
            parameters: vec![IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "Nat -> Bool -> IRScalarBox",
            body: "fun n b => IRScalarBox.mk n b",
            application: "let p := compiled large false; let q := compiled large true; (p.number, p.flag, q.number, q.flag)",
            expected: "(184467440737095516160, false, 184467440737095516160, true)",
            parameters: vec![IrType::TObject, IrType::UInt8],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRScalarBox -> Bool",
            body: "fun p => p.flag",
            application: "(compiled (IRScalarBox.mk large false), compiled (IRScalarBox.mk large true))",
            expected: "(false, true)",
            parameters: vec![IrType::Object],
            result: IrType::UInt8,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRInterleaved -> IRInterleaved",
            body: "fun p => IRInterleaved.mk p.second p.number p.first p.text",
            application: "let p := IRInterleaved.mk true large false heap; let q := compiled p; (q.first, q.second, q.number, q.text, p.number, p.text)",
            expected: "(false, true, 184467440737095516160, \"boxed heap payload\", 184467440737095516160, \"boxed heap payload\")",
            parameters: vec![IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "Bool -> Bool -> Bool -> IRAllBools",
            body: "fun a b c => IRAllBools.mk a b c",
            application: "let p := compiled true false true; let q := compiled false true false; (p.first, p.second, p.third, q.first, q.second, q.third)",
            expected: "(true, false, true, false, true, false)",
            parameters: vec![IrType::UInt8, IrType::UInt8, IrType::UInt8],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRAllBools -> Bool",
            body: "fun p => if p.first then p.third else p.second",
            application: "(compiled (IRAllBools.mk true false true), compiled (IRAllBools.mk true true false), compiled (IRAllBools.mk false true false))",
            expected: "(true, false, true)",
            parameters: vec![IrType::Object],
            result: IrType::UInt8,
            reduced: None,
        },
        BoxedExportCase {
            ty: "Bool -> IRScalarPayload",
            body: "fun b => IRScalarPayload.value b",
            application: "((match compiled false with | .empty => true | .value b => b), (match compiled true with | .empty => false | .value b => b))",
            expected: "(false, true)",
            parameters: vec![IrType::UInt8],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRScalarPayload -> IRScalarPayload",
            body: "fun p => p",
            application: "((match compiled .empty with | .empty => true | _ => false), (match compiled (.value false) with | .empty => true | .value b => b), (match compiled (.value true) with | .empty => false | .value b => b))",
            expected: "(true, false, true)",
            parameters: vec![IrType::TObject],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRScalarPayload -> Bool",
            body: "fun p => match p with | .empty => false | .value b => b",
            application: "(compiled .empty, compiled (.value false), compiled (.value true))",
            expected: "(false, false, true)",
            parameters: vec![IrType::TObject],
            result: IrType::UInt8,
            reduced: None,
        },
        BoxedExportCase {
            ty: "(IRInterleaved -> IRInterleaved) -> IRInterleaved -> IRInterleaved",
            body: "fun f p => f p",
            application: "let p := IRInterleaved.mk true large false heap; let q := compiled (fun x => IRInterleaved.mk x.second (x.number + 1) x.first (x.text ++ \"!\")) p; (q.first, q.second, q.number, q.text, p.number, p.text)",
            expected: "(false, true, 184467440737095516161, \"boxed heap payload!\", 184467440737095516160, \"boxed heap payload\")",
            parameters: vec![IrType::Object, IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "(IRScalarBox -> Bool) -> Nat -> Bool",
            body: "fun f n => f (IRScalarBox.mk n true)",
            application: "compiled (fun p => p.flag && p.number == large) large",
            expected: "true",
            parameters: vec![IrType::Object, IrType::TObject],
            result: IrType::UInt8,
            reduced: None,
        },
        BoxedExportCase {
            ty: "(IRScalarPayload -> Nat) -> Nat",
            body: "fun f => f IRScalarPayload.empty",
            application: "compiled (fun p => match p with | .empty => 42 | .value b => if b then 1 else 0)",
            expected: "42",
            parameters: vec![IrType::Object],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRInterleaved -> Nat -> Nat",
            body: "fun _ n => n",
            application: "compiled (IRInterleaved.mk true large false heap) 42",
            expected: "42",
            parameters: vec![IrType::Object, IrType::TObject],
            result: IrType::TObject,
            reduced: Some(("Nat -> Nat", "compiled 42")),
        },
        BoxedExportCase {
            ty: "IRAllBools -> Bool -> Bool",
            body: "fun _ b => b",
            application: "compiled (IRAllBools.mk true false true) true",
            expected: "true",
            parameters: vec![IrType::Object, IrType::UInt8],
            result: IrType::UInt8,
            reduced: Some(("Bool -> Bool", "compiled true")),
        },
        BoxedExportCase {
            ty: "IRNatWrapper",
            body: "IRNatWrapper.mk 42",
            application: "compiled.value",
            expected: "42",
            parameters: vec![],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "Nat -> IRNatWrapper",
            body: "fun n => IRNatWrapper.mk n",
            application: "((compiled 42).value, (compiled large).value, large)",
            expected: "(42, 184467440737095516160, 184467440737095516160)",
            parameters: vec![IrType::TObject],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRNatWrapper -> IRNatWrapper",
            body: "fun p => p",
            application: "let p := IRNatWrapper.mk large; let q := compiled p; ((compiled (IRNatWrapper.mk 42)).value, q.value, p.value)",
            expected: "(42, 184467440737095516160, 184467440737095516160)",
            parameters: vec![IrType::TObject],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRNatWrapper -> Nat",
            body: "fun p => match p with | .mk n => n",
            application: "let p := IRNatWrapper.mk large; (compiled p, p.value)",
            expected: "(184467440737095516160, 184467440737095516160)",
            parameters: vec![IrType::TObject],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "String -> IRStringWrapper",
            body: "fun s => IRStringWrapper.mk s",
            application: "let p := compiled heap; (p.value, heap)",
            expected: "(\"boxed heap payload\", \"boxed heap payload\")",
            parameters: vec![IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRStringWrapper -> IRStringWrapper",
            body: "fun p => IRStringWrapper.mk (p.value ++ p.value)",
            application: "let p := IRStringWrapper.mk heap; let q := compiled p; (q.value, p.value)",
            expected: "(\"boxed heap payloadboxed heap payload\", \"boxed heap payload\")",
            parameters: vec![IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRStringWrapper -> String",
            body: "fun p => p.value",
            application: "let p := IRStringWrapper.mk heap; (compiled p, p.value)",
            expected: "(\"boxed heap payload\", \"boxed heap payload\")",
            parameters: vec![IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "Bool -> IRBoolBox",
            body: "fun b => IRBoolBox.mk b",
            application: "((compiled false).value, (compiled true).value)",
            expected: "(false, true)",
            parameters: vec![IrType::UInt8],
            result: IrType::UInt8,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRBoolBox -> Bool",
            body: "fun p => p.value",
            application: "(compiled (IRBoolBox.mk false), compiled (IRBoolBox.mk true))",
            expected: "(false, true)",
            parameters: vec![IrType::UInt8],
            result: IrType::UInt8,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRBoolBox -> IRBoolBox",
            body: "fun p => match p with | .mk b => IRBoolBox.mk b",
            application: "((compiled (IRBoolBox.mk false)).value, (compiled (IRBoolBox.mk true)).value)",
            expected: "(false, true)",
            parameters: vec![IrType::UInt8],
            result: IrType::UInt8,
            reduced: None,
        },
        BoxedExportCase {
            ty: "(IRNatWrapper -> IRNatWrapper) -> IRNatWrapper -> IRNatWrapper",
            body: "fun f p => f p",
            application: "let p := IRNatWrapper.mk large; let q := compiled (fun x => IRNatWrapper.mk (x.value + 1)) p; (q.value, p.value)",
            expected: "(184467440737095516161, 184467440737095516160)",
            parameters: vec![IrType::Object, IrType::TObject],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "(IRBoolBox -> IRBoolBox) -> IRBoolBox -> IRBoolBox",
            body: "fun f p => f p",
            application: "let f := fun p : IRBoolBox => IRBoolBox.mk (if p.value then false else true); ((compiled f (IRBoolBox.mk false)).value, (compiled f (IRBoolBox.mk true)).value)",
            expected: "(true, false)",
            parameters: vec![IrType::Object, IrType::UInt8],
            result: IrType::UInt8,
            reduced: None,
        },
        BoxedExportCase {
            ty: "(IRStringWrapper -> String) -> String -> String",
            body: "fun f s => f (IRStringWrapper.mk s)",
            application: "(compiled (fun p => p.value ++ \"!\") heap, heap)",
            expected: "(\"boxed heap payload!\", \"boxed heap payload\")",
            parameters: vec![IrType::Object, IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "((Nat -> IRStringWrapper) -> IRStringWrapper) -> String -> IRStringWrapper",
            body: "fun use s => use (fun _ => IRStringWrapper.mk s)",
            application: "let p := compiled (fun f => f 42) heap; (p.value, heap)",
            expected: "(\"boxed heap payload\", \"boxed heap payload\")",
            parameters: vec![IrType::Object, IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRNatWrapper -> IRStringWrapper -> IRStringWrapper",
            body: "fun _ p => p",
            application: "let p := IRStringWrapper.mk heap; let q := compiled (IRNatWrapper.mk large) p; (q.value, p.value)",
            expected: "(\"boxed heap payload\", \"boxed heap payload\")",
            parameters: vec![IrType::TObject, IrType::Object],
            result: IrType::Object,
            reduced: Some((
                "IRStringWrapper -> IRStringWrapper",
                "let p := IRStringWrapper.mk heap; let q := compiled p; (q.value, p.value)",
            )),
        },
        BoxedExportCase {
            ty: "IRStringWrapper -> Nat -> Nat",
            body: "fun _ n => n",
            application: "compiled (IRStringWrapper.mk heap) 42",
            expected: "42",
            parameters: vec![IrType::Object, IrType::TObject],
            result: IrType::TObject,
            reduced: Some(("Nat -> Nat", "compiled 42")),
        },
        BoxedExportCase {
            ty: "IRBoolBox -> Nat -> Nat",
            body: "fun _ n => n",
            application: "compiled (IRBoolBox.mk true) 42",
            expected: "42",
            parameters: vec![IrType::UInt8, IrType::TObject],
            result: IrType::TObject,
            reduced: Some(("Nat -> Nat", "compiled 42")),
        },
    ]
}

fn recursive_export_cases() -> Vec<BoxedExportCase> {
    vec![
        BoxedExportCase {
            ty: "IRRecursive",
            body: "IRRecursive.next 7 (IRRecursive.next 9 IRRecursive.empty)",
            application: "match compiled with | .next n (.next m _) => n + m | _ => 0",
            expected: "16",
            parameters: vec![],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRRecursive -> IRRecursive",
            body: "fun p => p",
            application: "let p := IRRecursive.next large (.next 2 .empty); let q := compiled p; ((match q with | .next n (.next m _) => n + m | _ => 0), (match p with | .next n _ => n | _ => 0))",
            expected: "(184467440737095516162, 184467440737095516160)",
            parameters: vec![IrType::TObject],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRRecursive -> IRRecursive",
            body: "fun p => match p with | .empty => .empty | .next _ tail => tail",
            application: "let p := IRRecursive.next large (.next 2 .empty); ((match compiled .empty with | .empty => 0 | _ => 1), (match compiled p with | .next n _ => n | _ => 0), (match p with | .next n _ => n | _ => 0))",
            expected: "(0, 2, 184467440737095516160)",
            parameters: vec![IrType::TObject],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "(IRRecursive -> IRRecursive) -> IRRecursive -> IRRecursive",
            body: "fun f p => f p",
            application: "let p := IRRecursive.next large .empty; let q := compiled (fun tail => .next 3 tail) p; ((match q with | .next n (.next m _) => n + m | _ => 0), (match p with | .next n _ => n | _ => 0))",
            expected: "(184467440737095516163, 184467440737095516160)",
            parameters: vec![IrType::Object, IrType::TObject],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "Nat -> IRRecursive -> IRRecursive",
            body: "fun n tail => IRRecursive.next n tail",
            application: "let tail := IRRecursive.next 2 .empty; let p := compiled large tail; ((match p with | .next n (.next m _) => n + m | _ => 0), (match tail with | .next n _ => n | _ => 0))",
            expected: "(184467440737095516162, 2)",
            parameters: vec![IrType::TObject, IrType::TObject],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRRecursive -> Nat",
            body: "fun p => let rec total (xs : IRRecursive) : Nat := match xs with | .empty => 0 | .next n tail => n + total tail; total p",
            application: "let p := IRRecursive.next large (.next 2 (.next 3 .empty)); (compiled .empty, compiled p, (match p with | .next n _ => n | _ => 0))",
            expected: "(0, 184467440737095516165, 184467440737095516160)",
            parameters: vec![IrType::TObject],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRRecursiveFirst -> IRRecursiveFirst",
            body: "fun p => p",
            application: "((match compiled .empty with | .empty => 7 | _ => 0), (match compiled (.next large .empty) with | .next n _ => n | _ => 0))",
            expected: "(7, 184467440737095516160)",
            parameters: vec![IrType::TObject],
            result: IrType::TObject,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRRecursiveTree -> Bool -> IRRecursiveTree -> IRRecursiveTree",
            body: "fun left flag right => IRRecursiveTree.node left flag right",
            application: "let left := IRRecursiveTree.leaf large heap; let right := IRRecursiveTree.leaf 3 \"tail\"; match compiled left true right with | .node (.leaf n s) flag (.leaf m t) => (n + m, s, flag, t, (match left with | .leaf k _ => k | _ => 0)) | _ => (0, \"wrong\", false, \"wrong\", 0)",
            expected: "(184467440737095516163, \"boxed heap payload\", true, \"tail\", 184467440737095516160)",
            parameters: vec![IrType::Object, IrType::UInt8, IrType::Object],
            result: IrType::Object,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRRecursiveTree -> Bool",
            body: "fun p => match p with | .node left _ _ => (match left with | .node _ b _ => b | .leaf _ _ => false) | .leaf _ _ => false",
            application: "let leaf := IRRecursiveTree.leaf large heap; let p := IRRecursiveTree.node (.node leaf true leaf) false leaf; (compiled p, (match p with | .node _ b _ => b | _ => true))",
            expected: "(true, false)",
            parameters: vec![IrType::Object],
            result: IrType::UInt8,
            reduced: None,
        },
        BoxedExportCase {
            ty: "(IRRecursiveTree -> IRRecursiveTree) -> IRRecursiveTree -> Bool",
            body: "fun f p => match f p with | .node _ b _ => b | .leaf _ _ => false",
            application: "let p := IRRecursiveTree.leaf large heap; (compiled (fun t => .node t true t) p, (match p with | .leaf n s => (n, s) | _ => (0, \"wrong\")))",
            expected: "(true, 184467440737095516160, \"boxed heap payload\")",
            parameters: vec![IrType::Object, IrType::Object],
            result: IrType::UInt8,
            reduced: None,
        },
        BoxedExportCase {
            ty: "Nat -> (IRRecursiveTree -> IRRecursiveTree) -> IRRecursiveTree -> Bool",
            body: "fun _ f p => match f p with | .node _ b _ => b | .leaf _ _ => false",
            application: "let p := IRRecursiveTree.leaf large heap; (compiled 99 (fun t => .node t true t) p, (match p with | .leaf n s => (n, s) | _ => (0, \"wrong\")))",
            expected: "(true, 184467440737095516160, \"boxed heap payload\")",
            parameters: vec![IrType::TObject, IrType::Object, IrType::Object],
            result: IrType::UInt8,
            reduced: Some((
                "(IRRecursiveTree -> IRRecursiveTree) -> IRRecursiveTree -> Bool",
                "let p := IRRecursiveTree.leaf large heap; (compiled (fun t => .node t true t) p, (match p with | .leaf n s => (n, s) | _ => (0, \"wrong\")))",
            )),
        },
        BoxedExportCase {
            ty: "Bool -> (IRRecursiveTree -> IRRecursiveTree) -> IRRecursiveTree -> Bool",
            body: "fun fallback f p => match f p with | .node _ b _ => b | .leaf _ _ => fallback",
            application: "let p := IRRecursiveTree.leaf large heap; (compiled true (fun t => t) p, compiled false (fun t => t) p, compiled false (fun t => .node t true t) p, (match p with | .leaf n s => (n, s) | _ => (0, \"wrong\")))",
            expected: "(true, false, true, 184467440737095516160, \"boxed heap payload\")",
            parameters: vec![IrType::UInt8, IrType::Object, IrType::Object],
            result: IrType::UInt8,
            reduced: None,
        },
        BoxedExportCase {
            ty: "IRRecursive -> Nat -> Nat",
            body: "fun _ n => n",
            application: "compiled (IRRecursive.next large .empty) 42",
            expected: "42",
            parameters: vec![IrType::TObject, IrType::TObject],
            result: IrType::TObject,
            reduced: Some(("Nat -> Nat", "compiled 42")),
        },
    ]
}

fn boxed_base() -> Engine {
    enum_base()
        .check_source_files(
            &[BOXED_DATA_HELPERS.as_bytes()],
            &KVMap::new(),
            fln::SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

fn name(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn limits() -> EngineExecutionLimits {
    EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn base() -> Engine {
    let limits = limits();
    let options = KVMap::new();
    let seed = Engine::with_source_seed(EngineAdmissionLimits::new(limits.kernel))
        .unwrap()
        .into_complete()
        .unwrap();
    seed.execute_source_definitions(
        &[HELPERS.as_bytes(), INTERNAL_DATA_HELPERS.as_bytes()],
        &options,
        limits,
    )
    .unwrap()
    .into_complete()
    .unwrap()
    .engine
}

fn cases() -> [(&'static str, &'static str, &'static str); 5] {
    [
        ("Nat", "42", "42"),
        ("Nat", "184467440737095516160", "184467440737095516160"),
        ("String", "\"native IR\"", "\"native IR\""),
        ("Nat", "invoke (fun x => keep x) 42", "42"),
        (
            "String",
            "let saved := \"captured IR\"; invokeString (fun _ => saved) 7",
            "\"captured IR\"",
        ),
    ]
}

// Source type, body, downstream application, result type/value, source arity.
fn export_cases() -> [(
    &'static str,
    &'static str,
    &'static str,
    &'static str,
    &'static str,
    usize,
); 58] {
    [
        ("Nat", "42", "compiled", "Nat", "42", 0),
        (
            "String",
            "\"source export\"",
            "compiled",
            "String",
            "\"source export\"",
            0,
        ),
        ("Nat -> Nat", "fun x => x", "compiled 42", "Nat", "42", 1),
        (
            "Nat -> Nat",
            "fun x => x",
            "compiled 184467440737095516160",
            "Nat",
            "184467440737095516160",
            1,
        ),
        (
            "String -> String",
            "fun x => x",
            "compiled \"caller string\"",
            "String",
            "\"caller string\"",
            1,
        ),
        (
            "(Nat -> String) -> Nat -> String",
            "fun f x => f x",
            "compiled (fun _ => \"caller callback\") 7",
            "String",
            "\"caller callback\"",
            2,
        ),
        (
            "Nat -> String",
            "let saved := \"source capture\"; fun _ => saved",
            "compiled 7",
            "String",
            "\"source capture\"",
            1,
        ),
        (
            "Nat -> Nat -> Nat",
            "fun x _ => x",
            "compiled 184467440737095516160 5",
            "Nat",
            "184467440737095516160",
            2,
        ),
        (
            "Nat -> Nat",
            "fun x => x",
            "(fun (f : Nat -> Nat) => f 42) compiled",
            "Nat",
            "42",
            1,
        ),
        (
            "Nat -> Nat -> String",
            "fun _ => let saved := \"partial capture\"; fun _ => saved",
            "let f := compiled 7; f 9",
            "String",
            "\"partial capture\"",
            2,
        ),
        (
            "String -> Nat -> Nat",
            "fun _ x => x",
            "compiled \"unused\" 42",
            "Nat",
            "42",
            2,
        ),
        (
            "Nat -> Nat -> Nat -> Nat",
            "fun _ x _ => x",
            "compiled 7 184467440737095516160 9",
            "Nat",
            "184467440737095516160",
            3,
        ),
        (
            "Nat -> String -> String",
            "fun _ x => x",
            "compiled 7 \"retained string\"",
            "String",
            "\"retained string\"",
            2,
        ),
        (
            "∀ (x : Nat), x = x -> Nat",
            "fun x _ => x",
            "compiled 42 rfl",
            "Nat",
            "42",
            2,
        ),
        (
            "(0 = 0) -> String",
            "fun _ => \"erased proof\"",
            "compiled rfl",
            "String",
            "\"erased proof\"",
            1,
        ),
        (
            "Type -> Nat -> Nat",
            "fun _ x => x",
            "compiled String 184467440737095516160",
            "Nat",
            "184467440737095516160",
            2,
        ),
        (
            "Prop -> Nat -> Nat",
            "fun _ x => x",
            "compiled (0 = 0) 42",
            "Nat",
            "42",
            2,
        ),
        (
            "Type -> Nat",
            "fun _ => 42",
            "compiled String",
            "Nat",
            "42",
            1,
        ),
        (
            "(0 = 0) -> Nat",
            "fun _ => 42",
            "compiled rfl",
            "Nat",
            "42",
            1,
        ),
        (
            "Type -> String -> String",
            "fun _ x => x",
            "compiled Nat \"erased type string\"",
            "String",
            "\"erased type string\"",
            2,
        ),
        (
            "Type -> Nat -> String",
            "fun _ => let saved := \"type-slot capture\"; fun _ => saved",
            "let f := compiled String; f 7",
            "String",
            "\"type-slot capture\"",
            2,
        ),
        (
            "Nat -> Type -> Nat",
            "fun x _ => x",
            "compiled 184467440737095516160 String",
            "Nat",
            "184467440737095516160",
            2,
        ),
        (
            "Type -> (Nat -> String) -> Nat -> String",
            "fun _ f x => f x",
            "compiled Nat (fun _ => \"typed callback\") 7",
            "String",
            "\"typed callback\"",
            3,
        ),
        ("Bool", "true", "compiled", "Bool", "true", 0),
        ("Bool", "false", "compiled", "Bool", "false", 0),
        (
            "Bool -> Bool",
            "fun x => x",
            "compiled true",
            "Bool",
            "true",
            1,
        ),
        (
            "Bool -> Bool",
            "fun x => x",
            "compiled false",
            "Bool",
            "false",
            1,
        ),
        (
            "Bool -> Bool",
            "fun x => x",
            "(fun (f : Bool -> Bool) => f false) compiled",
            "Bool",
            "false",
            1,
        ),
        (
            "Bool -> Nat -> Nat",
            "fun _ x => x",
            "compiled false 42",
            "Nat",
            "42",
            2,
        ),
        (
            "Nat -> Bool -> Bool",
            "fun _ x => x",
            "compiled 7 true",
            "Bool",
            "true",
            2,
        ),
        (
            "(Bool -> Bool) -> Bool -> Bool",
            "fun f x => f x",
            "compiled (fun _ => false) true",
            "Bool",
            "false",
            2,
        ),
        (
            "Type -> Bool -> Bool",
            "fun _ x => x",
            "compiled Nat true",
            "Bool",
            "true",
            2,
        ),
        (
            "Bool -> String -> String",
            "fun _ x => x",
            "compiled true \"retained Boolean string\"",
            "String",
            "\"retained Boolean string\"",
            2,
        ),
        (
            "Bool -> Bool",
            "fun _ => true",
            "compiled false",
            "Bool",
            "true",
            1,
        ),
        (
            "Bool -> Bool -> Bool",
            "fun x _ => x",
            "compiled true false",
            "Bool",
            "true",
            2,
        ),
        (
            "(Bool -> Bool) -> Bool -> Bool",
            "fun f x => f x",
            "compiled (fun x => x) true",
            "Bool",
            "true",
            2,
        ),
        (
            "Bool -> Nat",
            "fun b => if b then 42 else 7",
            "compiled true",
            "Nat",
            "42",
            1,
        ),
        (
            "Bool -> Nat",
            "fun b => if b then 42 else 7",
            "compiled false",
            "Nat",
            "7",
            1,
        ),
        (
            "Bool -> String",
            "fun b => if b then \"yes branch\" else \"no branch\"",
            "compiled true",
            "String",
            "\"yes branch\"",
            1,
        ),
        (
            "Bool -> String",
            "fun b => if b then \"yes branch\" else \"no branch\"",
            "compiled false",
            "String",
            "\"no branch\"",
            1,
        ),
        (
            "Nat -> Nat",
            "fun n => n + 1",
            "compiled 41",
            "Nat",
            "42",
            1,
        ),
        (
            "Nat -> Nat",
            "fun n => n + 1",
            "compiled 184467440737095516160",
            "Nat",
            "184467440737095516161",
            1,
        ),
        (
            "Nat -> Bool",
            "fun n => Nat.beq n 42",
            "compiled 42",
            "Bool",
            "true",
            1,
        ),
        (
            "Nat -> Bool",
            "fun n => Nat.beq n 42",
            "compiled 184467440737095516160",
            "Bool",
            "false",
            1,
        ),
        (
            "Bool -> Nat -> Nat -> Nat",
            "fun b x y => if b then x else y",
            "compiled true 42 7",
            "Nat",
            "42",
            3,
        ),
        (
            "Bool -> Nat -> Nat -> Nat",
            "fun b x y => if b then x else y",
            "compiled false 7 184467440737095516160",
            "Nat",
            "184467440737095516160",
            3,
        ),
        (
            "String -> String",
            "fun text => String.append text \"!\"",
            "compiled \"native\"",
            "String",
            "\"native!\"",
            1,
        ),
        (
            "Nat -> Nat",
            "fun n => if Nat.beq n 0 then 7 else n + 1",
            "compiled 0",
            "Nat",
            "7",
            1,
        ),
        (
            "Nat -> Nat",
            "fun n => if Nat.beq n 0 then 7 else n + 1",
            "compiled 41",
            "Nat",
            "42",
            1,
        ),
        (
            "Nat -> Nat",
            "fun n => if Nat.beq n 0 then 7 else n + 1",
            "compiled 184467440737095516160",
            "Nat",
            "184467440737095516161",
            1,
        ),
        (
            "Bool -> Nat",
            "fun b => if b then (if b then 42 else 7) else 99",
            "compiled true",
            "Nat",
            "42",
            1,
        ),
        (
            "Bool -> Nat -> String",
            "fun b _ => if b then \"yes\" else \"no\"",
            "compiled false 7",
            "String",
            "\"no\"",
            2,
        ),
        (
            "String -> String",
            "fun s => (IRTextPair.mk s s).right",
            "compiled \"kept field\"",
            "String",
            "\"kept field\"",
            1,
        ),
        (
            "String -> String",
            "fun s => (IRTextPair.mk \"discarded field\" s).right",
            "compiled \"second field\"",
            "String",
            "\"second field\"",
            1,
        ),
        (
            "(Nat -> Nat) -> Nat",
            "fun f => (IRFunctionBox.mk f).run 184467440737095516160",
            "compiled (fun n => n)",
            "Nat",
            "184467440737095516160",
            1,
        ),
        (
            "String -> String",
            "fun s => (IRNested.mk (IRTextPair.mk s s)).pair.right",
            "compiled \"nested field\"",
            "String",
            "\"nested field\"",
            1,
        ),
        (
            "Bool -> Bool",
            "fun b => (IRBoolBox.mk b).value",
            "compiled true",
            "Bool",
            "true",
            1,
        ),
        (
            "Bool -> Bool",
            "fun b => (IRBoolBox.mk b).value",
            "compiled false",
            "Bool",
            "false",
            1,
        ),
    ]
}

fn erased_positions(index: usize) -> &'static [usize] {
    match index {
        13 | 21 => &[1],
        14..=20 => &[0],
        22 | 31 => &[0],
        _ => &[],
    }
}

fn boolean_positions(index: usize) -> &'static [usize] {
    match index {
        25..=28 | 32 | 33 | 36..=39 | 44 | 45 | 50 | 51 | 56 | 57 => &[0],
        29..=31 | 35 => &[1],
        34 => &[0, 1],
        _ => &[],
    }
}

fn checked_definition(base: &Engine, source: &str) -> (fln::Declaration, Engine) {
    let checked = base
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            fln::SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        )
        .unwrap_or_else(|e| panic!("{source}: {e:?}"))
        .into_complete()
        .unwrap();
    let environment = checked.engine.environment();
    let fln::ConstantInfo::Defn(definition) = environment.find(&name("compiled")).unwrap() else {
        panic!("source definition")
    };
    (fln::Declaration::Defn(definition.clone()), checked.engine)
}

fn assert_definition_admission(
    base: &Engine,
    checked: &Engine,
    compiled: &ir::DefinitionCompilation,
    options: &KVMap,
) {
    // Source checking also records equations and local-recursion auxiliaries.
    // The IR API receives only the Declaration, so its receipt must equal an
    // independent admission of that exact declaration. Keep the full source
    // snapshot as the execution oracle; compare the complete independent and
    // compiler admission environments in both directions.
    let fln::Declaration::Defn(definition) = &compiled.admission.declaration else {
        panic!("compiled source definition")
    };
    let Some(fln::ConstantInfo::Defn(source)) = checked.environment().find(&definition.base.name)
    else {
        panic!("source definition identity")
    };
    assert_eq!(
        definition, source,
        "compiler must admit the unchanged source body"
    );
    let original = base.logical_root(options);
    let expected = base
        .admit_declaration(
            compiled.admission.declaration.clone(),
            options,
            EngineAdmissionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let admitted = compiled.admission.engine.environment();
    for (name, value) in expected.engine.environment().constants() {
        assert_eq!(
            admitted.find(name),
            Some(value),
            "independently admitted declaration {name:?}"
        );
    }
    for (name, value) in admitted.constants() {
        assert_eq!(
            expected.engine.environment().find(name),
            Some(value),
            "unexpected compiler declaration {name:?}",
        );
    }
    assert_eq!(compiled.admission.base_logical_root, original);
    assert_eq!(compiled.admission.admissions.len(), 1);
    assert_eq!(
        compiled.admission.result_logical_root,
        expected.result_logical_root
    );
    assert_eq!(
        compiled.admission.engine.logical_root(options),
        expected.engine.logical_root(options),
    );
    assert_eq!(base.logical_root(options), original);
}

#[test]
fn arbitrary_fir_cannot_claim_the_closed_source_constructor_boundary() {
    use fln_comp::fir::*;
    let value = ValueId::new;
    let constructor = ConstructorId::new(0);
    let program = fln_comp::fir::validate(
        Program::new(
            FunctionId::new(0),
            vec![ConstructorDecl {
                id: constructor,
                tag: 0,
                fields: vec![ValueType::Bool],
                static_scalar_bytes: vec![],
            }],
            vec![],
            vec![],
            vec![Function {
                id: FunctionId::new(0),
                parameters: vec![],
                parameter_ownership: vec![],
                result: ValueType::Constructor,
                result_ownership: fln_comp::flbc::CallableResultOwnership::Owned,
                blocks: vec![Block {
                    id: BlockId::new(0),
                    bindings: vec![
                        Binding {
                            id: value(0),
                            ty: ValueType::Bool,
                            operation: Operation::Bool(false),
                        },
                        Binding {
                            id: value(1),
                            ty: ValueType::Constructor,
                            operation: Operation::Ctor {
                                constructor,
                                fields: vec![value(0)],
                            },
                        },
                    ],
                    terminator: Terminator::Return { value: value(1) },
                }],
            }],
        ),
        ValidationLimits::default(),
    )
    .unwrap();
    assert!(matches!(
        ir::compile(&program, &name("untrustedEntry"), CompileLimits::default()),
        Err(ir::CompileError::Unsupported {
            what: "non-pure boxed carrier"
        })
    ));
}

fn private_data_operations(module: &fln_olean::ir::IrModule) -> (usize, usize) {
    let mut constructors = 0;
    let mut projections = 0;
    let mut pending: Vec<_> = module
        .decls
        .iter()
        .filter_map(|declaration| {
            if let IrDecl::Function { body, .. } = declaration {
                Some(body)
            } else {
                None
            }
        })
        .collect();
    while let Some(body) = pending.pop() {
        for statement in &body.stmts {
            match statement {
                IrStmt::VDecl {
                    expr: IrExpr::Ctor { .. },
                    ..
                } => constructors += 1,
                IrStmt::VDecl {
                    expr: IrExpr::Proj { .. },
                    ..
                } => projections += 1,
                IrStmt::JDecl { value, .. } => pending.push(value),
                _ => {}
            }
        }
        if let IrTerminal::Case { alts, .. } = body.terminal.as_ref() {
            for alternative in alts {
                let body = match alternative {
                    fln_olean::ir::IrAlt::Ctor { body, .. }
                    | fln_olean::ir::IrAlt::Default { body } => body,
                };
                pending.push(body);
            }
        }
    }
    (constructors, projections)
}

#[test]
fn fieldless_enum_exports_preserve_scalar_signatures_and_private_layouts() {
    let base = enum_base();
    let options = KVMap::new();
    let original = base.logical_root(&options);
    let mut no_execution = limits();
    no_execution.vm.max_steps = 0;
    for case in enum_export_cases() {
        let source = format!("def compiled : {} := {}", case.ty, case.body);
        let (declaration, checked) = checked_definition(&base, &source);
        let compiled = ir::compile_source_definition(
            &base,
            declaration.clone(),
            &options,
            no_execution,
            CompileLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .into_complete()
        .unwrap();
        assert_definition_admission(&base, &checked, &compiled, &options);
        let IrDecl::Function { params, result, .. } = compiled
            .module
            .decls
            .iter()
            .find(|declaration| declaration.name() == &name("compiled"))
            .unwrap()
        else {
            panic!("enum source entry")
        };
        assert_eq!(
            params
                .iter()
                .map(|param| param.ty.clone())
                .collect::<Vec<_>>(),
            case.parameters,
            "{source}",
        );
        assert_eq!(*result, case.result, "{source}");
        assert_eq!(
            compiled
                .module
                .decls
                .iter()
                .any(|declaration| declaration.name() == &name("compiled._redArg")),
            case.reduced.is_some(),
            "{source}",
        );
        if case.body.contains("IREnumBox.mk") {
            let (constructors, projections) = private_data_operations(&compiled.module);
            assert!(constructors > 0 && projections > 0);
        }
        assert!(matches!(
            ir::compile_source_definition(
                &base,
                declaration,
                &options,
                no_execution,
                CompileLimits {
                    max_work: 0,
                    ..CompileLimits::default()
                },
            ),
            Err(ir::DefinitionCompileError::Ir(ir::CompileError::Limit))
        ));
        assert_eq!(base.logical_root(&options), original);
    }
    for source in [
        "def compiled (x : IRParameterized Nat) : IRParameterized Nat := x",
        "def compiled (x : IRAlias) : IRAlias := x",
        "def compiled : True := True.intro",
    ] {
        let (declaration, _) = checked_definition(&base, source);
        assert!(
            matches!(
                ir::compile_source_definition(
                    &base,
                    declaration,
                    &options,
                    limits(),
                    CompileLimits::default(),
                ),
                Err(ir::DefinitionCompileError::Ir(
                    ir::CompileError::Unsupported {
                        what: "source export carrier",
                    }
                ))
            ),
            "unsupported enum layout must refuse: {source}",
        );
        assert_eq!(base.logical_root(&options), original);
    }
}

#[test]
fn recursive_enum_calls_keep_their_private_dispatch_domains_without_execution() {
    let options = KVMap::new();
    let base = enum_base()
        .check_source_files(
            &[
                br#"partial def carryIRChoice (n : Nat) (value : IRChoice) : IRChoice :=
  if n == 0 then value else carryIRChoice (n - 1) value
partial def resetIRChoice (n : Nat) (value : IRChoice) : IRChoice :=
  if n == 0 then value else resetIRChoice (n - 1) IRChoice.west
"#,
            ],
            &options,
            fln::SourceCheckLimits::new(EngineAdmissionLimits::new(limits().kernel)),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let original = base.logical_root(&options);
    let mut no_execution = limits();
    no_execution.vm.max_steps = 0;
    // IRChoice reserves three tags. The generated Decidable dispatcher must
    // retain its actual two-constructor input domain across private calls.
    for callee in ["carryIRChoice", "resetIRChoice"] {
        let source = format!("def compiled (n : Nat) : IRChoice := {callee} n IRChoice.east");
        let (declaration, checked) = checked_definition(&base, &source);
        let compiled = ir::compile_source_definition(
            &base,
            declaration,
            &options,
            no_execution,
            CompileLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .into_complete()
        .unwrap();
        let IrDecl::Function { params, result, .. } = compiled
            .module
            .decls
            .iter()
            .find(|declaration| declaration.name() == &name("compiled"))
            .unwrap()
        else {
            panic!("recursive enum source entry")
        };
        assert_eq!(
            params.iter().map(|p| p.ty.clone()).collect::<Vec<_>>(),
            [IrType::TObject]
        );
        assert_eq!(*result, IrType::UInt8);
        assert_definition_admission(&base, &checked, &compiled, &options);
        assert_eq!(base.logical_root(&options), original);
    }
}

#[test]
fn boxed_data_exports_preserve_source_layouts_and_reduced_arguments() {
    let base = boxed_base();
    let options = KVMap::new();
    let original = base.logical_root(&options);
    let mut no_execution = limits();
    no_execution.vm.max_steps = 0;
    for case in boxed_export_cases()
        .into_iter()
        .chain(recursive_export_cases())
    {
        let source = format!("def compiled : {} := {}", case.ty, case.body);
        let (declaration, checked) = checked_definition(&base, &source);
        let compiled = ir::compile_source_definition(
            &base,
            declaration.clone(),
            &options,
            no_execution,
            CompileLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .into_complete()
        .unwrap();
        assert_definition_admission(&base, &checked, &compiled, &options);
        let IrDecl::Function { params, result, .. } = compiled
            .module
            .decls
            .iter()
            .find(|declaration| declaration.name() == &name("compiled"))
            .unwrap()
        else {
            panic!("boxed source entry")
        };
        assert_eq!(
            params
                .iter()
                .map(|parameter| parameter.ty.clone())
                .collect::<Vec<_>>(),
            case.parameters,
            "{source}",
        );
        assert_eq!(*result, case.result, "{source}");
        assert_eq!(
            compiled
                .module
                .decls
                .iter()
                .any(|declaration| { declaration.name() == &name("compiled._redArg") }),
            case.reduced.is_some(),
            "{source}",
        );
        if case.body.contains("IRFunctionBox.mk") {
            let (constructors, projections) = private_data_operations(&compiled.module);
            assert!(constructors > 0 && projections > 0);
        }
        if case.ty.contains("Wrapper") || case.ty.contains("IRBoolBox") {
            assert_eq!(
                private_data_operations(&compiled.module),
                (0, 0),
                "single-field wrappers must not allocate or project a constructor: {source}",
            );
        }
        assert!(matches!(
            ir::compile_source_definition(
                &base,
                declaration,
                &options,
                no_execution,
                CompileLimits {
                    max_work: 0,
                    ..CompileLimits::default()
                },
            ),
            Err(ir::DefinitionCompileError::Ir(ir::CompileError::Limit))
        ));
        assert_eq!(base.logical_root(&options), original);
    }
    // Keep every exact input that this feature moves out of the old refusal
    // tables, in addition to their typed signature and runtime cases above.
    for source in [
        "def compiled (x : IRPayload) : IRPayload := x",
        "def compiled (x : IRRecursive) : IRRecursive := x",
        "def compiled (x : IRRecursiveLoop) : IRRecursiveLoop := x",
        "def compiled (x : IRScalarBox) : IRScalarBox := x",
        "def compiled (x : IRScalarPayload) : IRScalarPayload := x",
        "def compiled (f : IRScalarPayload -> Nat) : Nat := f IRScalarPayload.empty",
        "def compiled (f : IRPayload -> Nat) : Nat := f IRPayload.empty",
        "def compiled (p : IRTextPair) : String := p.right",
        "def compiled (s : String) : IRTextPair := IRTextPair.mk s s",
        "def compiled (f : IRTextPair -> String) : String := f (IRTextPair.mk \"a\" \"b\")",
        "def compiled (x : IRNatWrapper) : IRNatWrapper := x",
        "def compiled (x : IRStringWrapper) : IRStringWrapper := x",
        "def compiled (p : IRBoolBox) : Bool := p.value",
        "def compiled (f : IRBoolBox -> Nat) : Nat := f (IRBoolBox.mk true)",
    ] {
        let (declaration, _) = checked_definition(&base, source);
        ir::compile_source_definition(
            &base,
            declaration,
            &options,
            no_execution,
            CompileLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .into_complete()
        .unwrap();
        assert_eq!(base.logical_root(&options), original);
    }
    for (source, expected) in [
        (
            "def compiled (x : IRProofBox) : IRProofBox := x",
            "source export carrier",
        ),
        (
            "def compiled (_ : IRRecursiveFirst) (n : Nat) : Nat := n",
            "unused recursive source parameter",
        ),
        (
            "def compiled (_ : IRRecursiveLoop) (n : Nat) : Nat := n",
            "unused recursive source parameter",
        ),
        (
            "def compiled (f : IRRecursiveTree -> IRRecursiveTree) (p : IRRecursiveTree) : Bool := match f p with | .node _ _ _ => false | .leaf _ _ => false",
            "specializable source call",
        ),
        (
            "def compiled (p : IRRecursiveTree) (_ : Nat) : Bool := match IRRecursiveTree.node p true p with | .node _ b _ => b | .leaf _ _ => false",
            "specializable source call",
        ),
        (
            "def compiled (x : IRBoxedParam Nat) : IRBoxedParam Nat := x",
            "source export carrier",
        ),
        (
            "def compiled (x : IRBoxedAlias) : IRBoxedAlias := x",
            "source export carrier",
        ),
        (
            "def compiled (x : IRBoxedRecord) (_ : IRWideRecord) : IRBoxedRecord := x",
            "conflicting source constructor layouts",
        ),
        (
            "def compiled (x : IRScalarBox) (_ : IRBoxedRecord) : IRScalarBox := x",
            "conflicting source constructor layouts",
        ),
        (
            "def compiled (x : IRInterleaved) (_ : IRScalarReordered) : IRInterleaved := x",
            "conflicting source constructor layouts",
        ),
        (
            "def compiled (x : IRNatWrapper) (_ : IRBoxedRecord) : IRNatWrapper := x",
            "conflicting source constructor layouts",
        ),
        (
            "def compiled (x : IRNatWrapper) (_ : IRScalarPayload) : IRNatWrapper := x",
            "conflicting source constructor layouts",
        ),
        (
            "def compiled (f : IRBoxedRecord -> Nat) (_ : IRChoice) : Nat := f (IRBoxedRecord.mk 0 \"\")",
            "conflicting source constructor layouts",
        ),
    ] {
        let (declaration, _) = checked_definition(&base, source);
        let result = ir::compile_source_definition(
            &base,
            declaration,
            &options,
            limits(),
            CompileLimits::default(),
        );
        assert!(
            matches!(result, Err(ir::DefinitionCompileError::Ir(
                ir::CompileError::Unsupported { what }
            )) if what == expected),
            "unsupported boxed layout must refuse: {source}",
        );
        assert_eq!(base.logical_root(&options), original);
    }
}

#[test]
fn source_exports_keep_source_arguments_and_compile_without_execution() {
    let base = base();
    let options = KVMap::new();
    let original = base.logical_root(&options);
    for (index, (ty, expression, application, result_type, expected, arity)) in
        export_cases().into_iter().enumerate()
    {
        let source = format!("def compiled : {ty} := {expression}");
        let (declaration, checked) = checked_definition(&base, &source);
        let mut no_execution = limits();
        no_execution.vm.max_steps = 0;
        let compiled = ir::compile_source_definition(
            &base,
            declaration.clone(),
            &options,
            no_execution,
            CompileLimits::default(),
        )
        .unwrap_or_else(|e| panic!("{source}: {e:?}"))
        .into_complete()
        .unwrap();
        assert_eq!(compiled.entry, name("compiled"));
        if index >= 52 {
            let (constructors, projections) = private_data_operations(&compiled.module);
            assert!(
                constructors > 0 && projections > 0,
                "the private-data case must construct and project at runtime: {source}"
            );
        }
        assert_definition_admission(&base, &checked, &compiled, &options);
        let public = compiled
            .module
            .decls
            .iter()
            .find(|d| d.name() == &name("compiled"))
            .unwrap();
        let IrDecl::Function { params, result, .. } = public else {
            panic!("source function entry")
        };
        assert_eq!(params.len(), arity, "{source}");
        assert!(params.iter().all(|p| !p.borrow));
        assert_eq!(
            params
                .iter()
                .enumerate()
                .filter_map(|(i, p)| (p.ty == IrType::UInt8).then_some(i))
                .collect::<Vec<_>>(),
            boolean_positions(index),
            "the independently specified Boolean source slots are UInt8: {source}",
        );
        assert_eq!(
            *result,
            match result_type {
                "Bool" => IrType::UInt8,
                "Nat" => IrType::TObject,
                _ => IrType::Object,
            },
            "source result carrier: {source}",
        );
        assert_eq!(
            params
                .iter()
                .enumerate()
                .filter_map(|(i, p)| (p.ty == IrType::Erased).then_some(i))
                .collect::<Vec<_>>(),
            erased_positions(index),
            "erased source slots retain their exact positions: {source}",
        );
        if !erased_positions(index).is_empty() || !boolean_positions(index).is_empty() {
            let boxed = compiled
                .module
                .decls
                .iter()
                .find(|d| d.name() == &name("compiled._boxed"))
                .unwrap();
            let IrDecl::Function {
                params: boxed,
                result: boxed_result,
                ..
            } = boxed
            else {
                panic!("source boxed entry")
            };
            assert_eq!(boxed.len(), arity);
            for &position in erased_positions(index) {
                assert_eq!(boxed[position].ty, IrType::TObject);
            }
            for &position in boolean_positions(index) {
                assert_eq!(boxed[position].ty, IrType::Tagged);
            }
            if result_type == "Bool" {
                assert_eq!(*boxed_result, IrType::Tagged);
            }
        }
        let source = format!("def result : {result_type} := {application}");
        let executed = checked
            .execute_source_definitions(&[source.as_bytes()], &options, limits())
            .unwrap_or_else(|e| panic!("{source}: {e:?}"))
            .into_complete()
            .unwrap();
        let VmExit::Returned(value) = &executed.executions[0].exit else {
            panic!("native source application")
        };
        if result_type == "Nat" {
            assert_eq!(
                fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
                Some(expected)
            );
        } else if result_type == "Bool" {
            assert!(value.value.is_scalar());
            assert_eq!(value.value.unbox(), usize::from(expected == "true"));
        } else {
            let string = value.value.try_string_view().unwrap();
            assert_eq!(
                &string.3[..string.0 - 1],
                expected.trim_matches('"').as_bytes()
            );
        }
        assert!(matches!(
            ir::compile_source_definition(
                &base,
                declaration,
                &options,
                no_execution,
                CompileLimits {
                    max_work: 0,
                    ..CompileLimits::default()
                },
            ),
            Err(ir::DefinitionCompileError::Ir(ir::CompileError::Limit))
        ));
        assert_eq!(base.logical_root(&options), original);
    }
    // Retain the exact formerly unsupported input as a positive, including its
    // dependent proof domain, rather than merely dropping it from the negatives.
    let source = "def compiled (x : Nat) (_h : x = x) : Nat := x";
    let (declaration, checked) = checked_definition(&base, source);
    let compiled = ir::compile_source_definition(
        &base,
        declaration,
        &options,
        limits(),
        CompileLimits::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    assert_definition_admission(&base, &checked, &compiled, &options);
    assert_eq!(base.logical_root(&options), original);
    for source in [
        "def compiled {A : Type} (x : A) : A := x",
        "universe u\ndef compiled {A : Type u} (x : A) : A := x",
        "def compiled {A : Type} (x : A) : Nat := 42",
        "def compiled (P : Prop) : P -> P := fun x => x",
        "def compiled : Nat -> Type := fun _ => Nat",
        "def compiled : (Nat -> Nat) -> Nat -> Nat := invoke",
        "def compiled (x y : Nat) : Nat := keep x",
        "def compiled (f : Nat -> Nat) (x : Nat) : Nat := x",
        "def compiled (s : String) : IRNested := IRNested.mk (IRTextPair.mk s s)",
    ] {
        let (declaration, _) = checked_definition(&base, source);
        assert!(
            matches!(
                ir::compile_source_definition(
                    &base,
                    declaration,
                    &options,
                    limits(),
                    CompileLimits::default(),
                ),
                Err(ir::DefinitionCompileError::Ir(
                    ir::CompileError::Unsupported { .. }
                ))
            ),
            "{source}"
        );
        assert_eq!(base.logical_root(&options), original);
    }
    for (source, refused) in [
        (
            "def compiled (x y : Nat) : Nat := let b := true; if b then x else y",
            "local Boolean source discriminator",
        ),
        (
            "def compiled (h : Nat -> Nat) (b : Bool) : Nat := let x := 0; let y := 0; h (if b then x else y)",
            "local Boolean source arm",
        ),
    ] {
        let (declaration, _) = checked_definition(&base, source);
        assert!(
            matches!(
                ir::compile_source_definition(
                    &base,
                    declaration,
                    &options,
                    limits(),
                    CompileLimits::default(),
                ),
                Err(ir::DefinitionCompileError::Ir(ir::CompileError::Unsupported { what }))
                    if what == refused
            ),
            "a local constant must not change the guessed reduced ABI: {source}"
        );
        assert_eq!(base.logical_root(&options), original);
    }
    let (fln::Declaration::Defn(mut wrong), _) =
        checked_definition(&base, "def compiled : Nat := 42")
    else {
        panic!("ordinary definition")
    };
    wrong.value = fln_core::expr::Expr::lit(fln_core::expr::Literal::Str("not a Nat".into()));
    assert!(matches!(
        ir::compile_source_definition(
            &base,
            fln::Declaration::Defn(wrong),
            &options,
            limits(),
            CompileLimits::default(),
        ),
        Err(ir::DefinitionCompileError::Engine(_))
    ));
    assert_eq!(base.logical_root(&options), original);
}

struct NativeCallExportCase {
    ty: &'static str,
    expression: &'static str,
    application: &'static str,
    partial: &'static str,
    result_type: &'static str,
    expected: &'static str,
    reduced: Option<(&'static str, &'static str)>,
}

fn native_call_export_cases() -> Vec<NativeCallExportCase> {
    vec![
        NativeCallExportCase {
            ty: "Nat -> Nat -> Nat",
            expression: "fun x y => Nat.add x y",
            application: "compiled 17 25",
            partial: "let f := compiled 17; f 25",
            result_type: "Nat",
            expected: "42",
            reduced: None,
        },
        NativeCallExportCase {
            ty: "Nat -> Nat -> Nat",
            expression: "fun x y => x + y",
            application: "compiled 184467440737095516160 25",
            partial: "let f := compiled 184467440737095516160; f 25",
            result_type: "Nat",
            expected: "184467440737095516185",
            reduced: None,
        },
        NativeCallExportCase {
            ty: "Nat -> Nat -> Nat",
            expression: "fun x y => let saved := x + 2; saved + y",
            application: "compiled 19 21",
            partial: "let f := compiled 19; f 21",
            result_type: "Nat",
            expected: "42",
            reduced: None,
        },
        NativeCallExportCase {
            ty: "Nat -> Nat -> Nat",
            expression: "fun x y => let saved := x; saved",
            application: "compiled 42 99",
            partial: "let f := compiled 42; f 99",
            result_type: "Nat",
            expected: "42",
            reduced: Some(("Nat -> Nat", "compiled 42")),
        },
        NativeCallExportCase {
            ty: "Nat -> Nat -> Nat",
            expression: "fun x => let saved := x + 2; fun _ => saved",
            application: "compiled 40 99",
            partial: "let f := compiled 40; f 99",
            result_type: "Nat",
            expected: "42",
            reduced: Some(("Nat -> Nat", "compiled 40")),
        },
        NativeCallExportCase {
            ty: "Nat -> Nat -> Nat",
            expression: "fun x y => let unused := Nat.add x 5; y",
            application: "compiled 99 42",
            partial: "let f := compiled 99; f 42",
            result_type: "Nat",
            expected: "42",
            reduced: Some(("Nat -> Nat", "compiled 42")),
        },
        NativeCallExportCase {
            ty: "Nat -> Nat -> Nat",
            expression: "fun x y => let unused := Nat.add x y; 42",
            application: "compiled 99 7",
            partial: "let f := compiled 99; f 7",
            result_type: "Nat",
            expected: "42",
            reduced: None,
        },
        NativeCallExportCase {
            ty: "Nat -> Nat -> Nat",
            expression: "fun x y => let saved := x; let x := y; Nat.add saved x",
            application: "compiled 17 25",
            partial: "let f := compiled 17; f 25",
            result_type: "Nat",
            expected: "42",
            reduced: None,
        },
        NativeCallExportCase {
            ty: "Nat -> Nat -> Nat",
            expression: "fun x _ => Nat.add (Nat.add x 0) (Nat.add 1 1)",
            application: "compiled 40 99",
            partial: "let f := compiled 40; f 99",
            result_type: "Nat",
            expected: "42",
            reduced: Some(("Nat -> Nat", "compiled 40")),
        },
        NativeCallExportCase {
            ty: "String -> String -> String",
            expression: "fun x y => String.append x y",
            application: "compiled \"left \" \"right\"",
            partial: "let f := compiled \"left \"; f \"right\"",
            result_type: "String",
            expected: "\"left right\"",
            reduced: None,
        },
        NativeCallExportCase {
            ty: "String -> String -> String",
            expression: "fun x y => let saved := x ++ \"λ\"; saved ++ y",
            application: "compiled \"α\" \"β\"",
            partial: "let f := compiled \"α\"; f \"β\"",
            result_type: "String",
            expected: "\"αλβ\"",
            reduced: None,
        },
        NativeCallExportCase {
            ty: "String -> String -> String",
            expression: "fun x y => let unused := String.append x \"?\"; String.append y \"!\"",
            application: "compiled \"unused\" \"answer\"",
            partial: "let f := compiled \"unused\"; f \"answer\"",
            result_type: "String",
            expected: "\"answer!\"",
            reduced: Some(("String -> String", "compiled \"answer\"")),
        },
    ]
}

#[test]
fn source_exports_track_native_call_and_let_dependencies() {
    let base = base();
    let options = KVMap::new();
    let original = base.logical_root(&options);
    let mut no_execution = limits();
    no_execution.vm.max_steps = 0;
    for case in native_call_export_cases() {
        let source = format!("def compiled : {} := {}", case.ty, case.expression);
        let (declaration, checked) = checked_definition(&base, &source);
        let compiled = ir::compile_source_definition(
            &base,
            declaration.clone(),
            &options,
            no_execution,
            CompileLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .into_complete()
        .unwrap();
        assert_eq!(
            compiled
                .module
                .decls
                .iter()
                .any(|decl| decl.name() == &name("compiled._redArg")),
            case.reduced.is_some(),
            "{source}",
        );
        for application in [case.application, case.partial] {
            let source = format!("def result : {} := {application}", case.result_type);
            let run = checked
                .execute_source_definitions(&[source.as_bytes()], &options, limits())
                .unwrap_or_else(|error| panic!("{source}: {error:?}"))
                .into_complete()
                .unwrap();
            let VmExit::Returned(value) = &run.executions[0].exit else {
                panic!("native source application")
            };
            if case.result_type == "Nat" {
                assert_eq!(
                    fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
                    Some(case.expected)
                );
            } else {
                let string = value.value.try_string_view().unwrap();
                assert_eq!(
                    &string.3[..string.0 - 1],
                    case.expected.trim_matches('"').as_bytes()
                );
            }
        }
        let bounded = ir::compile_source_definition(
            &base,
            declaration,
            &options,
            no_execution,
            CompileLimits {
                max_work: 100,
                ..CompileLimits::default()
            },
        );
        assert!(
            match bounded {
                Err(ir::DefinitionCompileError::Ir(ir::CompileError::Limit)) => true,
                Err(ir::DefinitionCompileError::Engine(fln::EngineExecutionError::Ingress(
                    error,
                ))) => error.is_resource_exhaustion(),
                _ => false,
            },
            "compiler exhaustion must stay a resource result: {source}"
        );
        assert_eq!(base.logical_root(&options), original);
    }
    for source in [
        "def compiled (x y : Nat) : Nat := Nat.add (Nat.mul x 0) y",
        "def compiled (x y : Nat) : Nat := let saved := Nat.sub 0 x; Nat.add saved y",
        "def compiled (f : Nat -> Nat) (x y : Nat) : Nat := let unused := Nat.add (f x) y; y",
        "def compiled (x y : Nat) : Nat := let f := fun _ : Nat => x; f y",
    ] {
        let (declaration, _) = checked_definition(&base, source);
        assert!(
            matches!(
                ir::compile_source_definition(
                    &base,
                    declaration,
                    &options,
                    no_execution,
                    CompileLimits::default()
                ),
                Err(ir::DefinitionCompileError::Ir(
                    ir::CompileError::Unsupported { .. }
                ))
            ),
            "unmodeled simplification must not choose an ABI: {source}"
        );
    }
}

#[test]
fn source_call_dependencies_do_not_trust_replaced_primitives_or_dictionaries() {
    use fln_elab::externs::{ExternEntry, register};
    let base = base();
    let options = KVMap::new();
    for (target, body, ty) in [
        ("Nat.add", "Nat.add x y", "Nat"),
        ("HAdd.hAdd", "x + y", "Nat"),
        ("instHAdd", "x + y", "Nat"),
        ("instAddNat", "x + y", "Nat"),
        ("HAdd.mk", "x + y", "Nat"),
        ("Add.mk", "x + y", "Nat"),
        ("String.append", "String.append x y", "String"),
        ("HAppend.hAppend", "x ++ y", "String"),
        ("instHAppendOfAppend", "x ++ y", "String"),
        ("instAppendString", "x ++ y", "String"),
        ("HAppend.mk", "x ++ y", "String"),
        ("Append.mk", "x ++ y", "String"),
    ] {
        let environment = register(
            base.environment(),
            &name(target),
            vec![ExternEntry::Standard {
                backend: name("all"),
                symbol: "unreviewed_source_operation".into(),
            }],
        )
        .unwrap();
        let changed = Engine::from_environment(environment);
        let source = format!("def compiled (x y : {ty}) : {ty} := {body}");
        let (declaration, _) = checked_definition(&changed, &source);
        assert!(
            matches!(
                ir::compile_source_definition(
                    &changed,
                    declaration,
                    &options,
                    limits(),
                    CompileLimits::default()
                ),
                Err(ir::DefinitionCompileError::Ir(
                    ir::CompileError::Unsupported { .. }
                ))
            ),
            "an explicit extern must invalidate dependency analysis for {target}"
        );
    }
    let environment =
        fln_elab::implemented_by::register(base.environment(), &name("Nat.add"), &name("Nat.sub"))
            .unwrap();
    let changed = Engine::from_environment(environment);
    let (declaration, _) =
        checked_definition(&changed, "def compiled (x y : Nat) : Nat := Nat.add x y");
    assert!(matches!(
        ir::compile_source_definition(
            &changed,
            declaration,
            &options,
            limits(),
            CompileLimits::default()
        ),
        Err(ir::DefinitionCompileError::Ir(
            ir::CompileError::Unsupported { .. }
        ))
    ));
}

// Valid FIR permits a borrowed argument to alias a consumed argument. Unlike
// source parameters (normally borrowed), this exercises that mixed contract
// directly, with a freshly allocated closure whose last owner is transferred.
fn aliased_borrow_program(tail: bool) -> fln_comp::fir::ValidatedProgram {
    use fln_comp::fir::{self, *};
    use fln_comp::flbc::{ArgumentOwnership as A, CallableResultOwnership as R};
    let v = ValueId::new;
    let f = FunctionId::new;
    let signature = ClosureTypeId::new(0);
    let closure = ValueType::Closure(signature);
    let binding = |id, ty, operation| Binding {
        id: v(id),
        ty,
        operation,
    };
    let apply = |closure, arg| Operation::Apply {
        closure: v(closure),
        args: vec![v(arg)],
        argument_ownership: vec![A::Borrowed],
        result_ownership: R::Owned,
    };
    let block = |bindings, result| {
        vec![Block {
            id: BlockId::new(0),
            bindings,
            terminator: Terminator::Return { value: v(result) },
        }]
    };
    let mut entry = vec![
        binding(
            0,
            ValueType::String,
            Operation::String("aliased borrow".into()),
        ),
        binding(
            1,
            closure,
            Operation::Closure {
                closure_type: signature,
                function: f(2),
                captures: vec![v(0)],
                capture_ownership: vec![A::Borrowed],
            },
        ),
        binding(
            2,
            if tail { ValueType::String } else { closure },
            Operation::Call {
                function: f(1),
                args: vec![v(1), v(1)],
            },
        ),
    ];
    if !tail {
        entry.push(binding(3, ValueType::Nat, Operation::Nat(7)));
        entry.push(binding(4, ValueType::String, apply(2, 3)));
    }
    let alias_body = if tail {
        block(
            vec![
                binding(2, ValueType::Nat, Operation::Nat(7)),
                binding(3, ValueType::String, apply(1, 2)),
            ],
            3,
        )
    } else {
        block(vec![], 1)
    };
    fir::validate(
        Program::new_with_closures(
            f(0),
            vec![],
            vec![],
            vec![ClosureTypeDecl {
                id: signature,
                parameters: vec![ValueType::Nat],
                parameter_ownership: vec![A::Borrowed],
                result: ValueType::String,
                result_ownership: R::Owned,
            }],
            vec![],
            vec![
                Function {
                    id: f(0),
                    parameters: vec![],
                    parameter_ownership: vec![],
                    result: ValueType::String,
                    result_ownership: R::Owned,
                    blocks: block(entry, if tail { 2 } else { 4 }),
                },
                Function {
                    id: f(1),
                    parameters: vec![closure, closure],
                    parameter_ownership: vec![A::Owned, A::Borrowed],
                    result: if tail { ValueType::String } else { closure },
                    result_ownership: R::Owned,
                    blocks: alias_body,
                },
                Function {
                    id: f(2),
                    parameters: vec![ValueType::String, ValueType::Nat],
                    parameter_ownership: vec![A::Borrowed, A::Borrowed],
                    result: ValueType::String,
                    result_ownership: R::Owned,
                    blocks: block(vec![], 0),
                },
            ],
        ),
        ValidationLimits::default(),
    )
    .unwrap()
}

fn cached_closure_program() -> fln_comp::fir::ValidatedProgram {
    use fln_comp::fir::{self, *};
    use fln_comp::flbc::{ArgumentOwnership as A, CallableResultOwnership as R};
    let template = aliased_borrow_program(false);
    let closure = ValueType::Closure(ClosureTypeId::new(0));
    let v = ValueId::new;
    let binding = |id, ty, operation| Binding {
        id: v(id),
        ty,
        operation,
    };
    let call = || Operation::Call {
        function: FunctionId::new(1),
        args: vec![],
    };
    let apply = |id| Operation::Apply {
        closure: v(id),
        args: vec![v(1)],
        argument_ownership: vec![A::Borrowed],
        result_ownership: R::Owned,
    };
    let block = |bindings, result| {
        vec![Block {
            id: BlockId::new(0),
            bindings,
            terminator: Terminator::Return { value: v(result) },
        }]
    };
    let mut functions = template.functions().to_vec();
    functions[0].blocks = block(
        vec![
            binding(0, closure, call()),
            binding(1, ValueType::Nat, Operation::Nat(7)),
            binding(2, ValueType::String, apply(0)),
            binding(3, closure, call()),
            binding(4, ValueType::String, apply(3)),
        ],
        4,
    );
    functions[1] = Function {
        id: FunctionId::new(1),
        parameters: vec![],
        parameter_ownership: vec![],
        result: closure,
        result_ownership: R::Owned,
        blocks: block(
            vec![
                binding(
                    0,
                    ValueType::String,
                    Operation::String("cached closure".into()),
                ),
                binding(
                    1,
                    closure,
                    Operation::Closure {
                        closure_type: ClosureTypeId::new(0),
                        function: FunctionId::new(2),
                        captures: vec![v(0)],
                        capture_ownership: vec![A::Borrowed],
                    },
                ),
            ],
            1,
        ),
    };
    fir::validate(
        Program::new_with_closures(
            FunctionId::new(0),
            vec![],
            vec![],
            template.closure_types().to_vec(),
            vec![],
            functions,
        ),
        ValidationLimits::default(),
    )
    .unwrap()
}

fn replace_result(params: &[fln_olean::ir::IrParam], body: &mut IrBody, ty: &str) {
    let mut stmts: Vec<_> = params
        .iter()
        .filter(|p| !p.borrow && p.ty != IrType::Erased && p.ty != IrType::UInt8)
        .map(|p| IrStmt::Dec {
            x: p.x,
            n: 1,
            checked: true,
            persistent: false,
        })
        .collect();
    let result = params.iter().map(|p| p.x).max().unwrap_or(0) + 1;
    stmts.push(IrStmt::VDecl {
        x: result,
        ty: if ty == "Nat" {
            IrType::Tagged
        } else {
            IrType::Object
        },
        expr: IrExpr::Lit(if ty == "Nat" {
            IrLit::Num(IrNat::Small(99))
        } else {
            IrLit::Str("changed IR".into())
        }),
    });
    *body = IrBody {
        stmts,
        terminal: Box::new(IrTerminal::Ret(IrArg::Var(result))),
    };
}

fn replace_boolean_result(
    params: &[fln_olean::ir::IrParam],
    body: &mut IrBody,
    carrier: IrType,
    value: bool,
) {
    let mut stmts: Vec<_> = params
        .iter()
        .filter(|p| !p.borrow && matches!(p.ty, IrType::Object | IrType::TObject | IrType::Tagged))
        .map(|p| IrStmt::Dec {
            x: p.x,
            n: 1,
            checked: true,
            persistent: false,
        })
        .collect();
    let x = params.iter().map(|p| p.x).max().unwrap_or(0) + 1;
    stmts.push(IrStmt::VDecl {
        x,
        ty: carrier,
        expr: IrExpr::Lit(IrLit::Num(IrNat::Small(u64::from(value)))),
    });
    *body = IrBody {
        stmts,
        terminal: Box::new(IrTerminal::Ret(IrArg::Var(x))),
    };
}

#[test]
fn admitted_definitions_compile_without_execution_and_keep_their_root() {
    let base = base();
    let options = KVMap::new();
    let original = base.logical_root(&options);
    for (ty, expression, expected) in cases() {
        let source = format!("def generated : {ty} := {expression}");
        let run = base
            .execute_source_definitions(&[source.as_bytes()], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap();
        let execution = &run.executions[0];
        let VmExit::Returned(value) = &execution.exit else {
            panic!("{source}: {:?}", execution.exit)
        };
        if ty == "Nat" {
            assert_eq!(
                fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
                Some(expected)
            );
        } else {
            assert_eq!(
                value.value.try_string_view().unwrap().3
                    [..value.value.try_string_view().unwrap().0 - 1],
                expected.trim_matches('"').as_bytes()[..]
            );
        }
        let mut no_execution = limits();
        no_execution.vm.max_steps = 0;
        let compiled = ir::compile_definition(
            &base,
            execution.declaration.clone(),
            &name("compiled"),
            &options,
            no_execution,
            CompileLimits::default(),
        )
        .unwrap_or_else(|e| panic!("{source}: {e:?}"))
        .into_complete()
        .unwrap();
        assert_eq!(
            compiled.admission.result_logical_root,
            run.result_logical_root
        );
        assert_eq!(base.logical_root(&options), original);
        fln_olean::ir_validate::validate_ir(
            std::slice::from_ref(&compiled.module),
            &BTreeMap::new(),
            Default::default(),
        )
        .unwrap();
        if expression.contains("invoke") {
            assert!(
                compiled.module.decls.len() > 2,
                "callbacks must reach the backend"
            );
            assert!(
                compiled.module.decls.iter().any(|d| match d {
                    IrDecl::Function { body, .. } => body.stmts.iter().any(|s| matches!(
                        s,
                        IrStmt::VDecl {
                            expr: IrExpr::Ap { .. },
                            ..
                        }
                    )),
                    _ => false,
                }),
                "the callback application cannot be folded out of this control"
            );
        }
        let stopped = ir::compile_definition(
            &base,
            execution.declaration.clone(),
            &name("compiled"),
            &options,
            no_execution,
            CompileLimits {
                max_work: 0,
                ..CompileLimits::default()
            },
        );
        assert!(matches!(
            stopped,
            Err(ir::DefinitionCompileError::Ir(ir::CompileError::Limit))
        ));
        assert_eq!(base.logical_root(&options), original);
    }
}

fn reference() -> Option<PathBuf> {
    let lean = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|p| {
                PathBuf::from(p).join(".elan/toolchains/leanprover--lean4---v4.32.0/bin/lean")
            })
        })?;
    lean.is_file().then_some(lean)
}

fn imported_strings(lib: &Path, stack: usize, module_root: &str) -> Engine {
    use fln::source_check::modules::imported::SourceOleanImportLimits;
    use fln::{
        Environment, OleanCheckLimits, OleanDecodeLimits, OleanFrontierJobs, OleanModuleInput,
    };

    type Parts = (Vec<u8>, Option<Vec<u8>>, Option<Vec<u8>>);
    let root = name(module_root);
    let mut pending = vec![root.clone()];
    let mut artifacts = BTreeMap::<Name, Parts>::new();
    while let Some(module) = pending.pop() {
        if artifacts.contains_key(&module) {
            continue;
        }
        let path = lib
            .join(module.to_display_string().replace('.', "/"))
            .with_extension("olean");
        let public = std::fs::read(&path).unwrap();
        pending.extend(fln::olean_module_imports(&public, OleanDecodeLimits::new(stack)).unwrap());
        let optional = |path| match std::fs::read(path) {
            Ok(bytes) => Some(bytes),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => panic!("read companion: {error}"),
        };
        artifacts.insert(
            module,
            (
                public,
                optional(path.with_extension("olean.server")),
                optional(path.with_extension("olean.private")),
            ),
        );
    }
    let inputs: Vec<_> = artifacts
        .iter()
        .map(|(name, (public, server, private))| OleanModuleInput {
            name,
            artifact: public,
            server_artifact: server.as_deref(),
            private_artifact: private.as_deref(),
        })
        .collect();
    let mut admission =
        SourceOleanImportLimits::new(OleanCheckLimits::new(stack, Budget::for_stack_bytes(stack)));
    admission.jobs = OleanFrontierJobs {
        threads: std::num::NonZeroUsize::new(1).unwrap(),
        worker_stack_bytes: stack,
    };
    Engine::from_environment(Environment::new())
        .import_olean_modules_for_source(&inputs, &[root], &KVMap::new(), admission)
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

fn encode(module: &fln_olean::ir::IrModule, original: &[u8]) -> Vec<u8> {
    let view = OleanView::parse(original).unwrap();
    let metadata = view.module_data(WalkBudget::default()).unwrap();
    let blocks = view
        .extension_payloads(WalkBudget::default(), 64 * 1024 * 1024)
        .unwrap();
    let extras: Vec<_> = blocks
        .iter()
        .filter(|b| b.name != name("Lean.IR.declMapExt") && b.name != name("Lean.regularInitAttr"))
        .map(|b| {
            (
                b.name.clone(),
                b.entries
                    .iter()
                    .map(|p| fln_rt::region::materialize(p, 0).unwrap())
                    .collect::<Vec<_>>(),
            )
        })
        .collect();
    let extensions: Vec<_> = extras
        .iter()
        .map(|(name, entries)| fln_olean::ModuleExtensionInput { name, entries })
        .collect();
    let mut extra_names: BTreeSet<_> = view
        .extra_const_names(WalkBudget::default())
        .unwrap()
        .into_iter()
        .collect();
    extra_names.extend(module.decls.iter().map(|d| d.name().clone()));
    let extra_names: Vec<_> = extra_names.into_iter().collect();
    encode_ir(
        IrWriteInput {
            module: ModuleWriteInput {
                is_module: metadata.is_module,
                imports: &metadata.imports,
                constants: &[],
                extra_const_names: &extra_names,
            },
            declarations: &module.decls,
            initializers: &module.initializers,
            additional_extensions: &extensions,
        },
        OleanWriteHeader {
            version: view.header.version,
            flags: view.header.flags,
            lean_version: &view.header.lean_version,
            githash: &view.header.githash,
            base_addr: view.header.base_addr,
        },
        IrWriteLimits::default(),
    )
    .unwrap()
    .bytes
}

fn consume(lean: &Path, dir: &Path) -> std::process::Output {
    Command::new(lean)
        .current_dir(dir)
        .env("LEAN_PATH", dir)
        .arg("Consumer.lean")
        .output()
        .unwrap()
}

struct RuntimeProbe<'a> {
    ty: &'a str,
    application: &'a str,
    entry: &'a str,
    check_meta: bool,
    higher_universe: bool,
    heap_call: Option<&'a str>,
}

fn consume_ir(
    lean: &Path,
    dir: &Path,
    label: &str,
    probe: &RuntimeProbe<'_>,
) -> std::process::Output {
    // Import only Lean statically. Loading the target and retrieving its value
    // at runtime prevents compiler inlining of logical companion bodies from
    // making an IR-body mutation invisible. Types come from the checked source
    // signature; generated reduced entries use independently specified cases.
    // The pin's public evalConst fixes its value universe at Type 0. A source
    // type such as Type -> Nat -> Nat is in Type 1. Lift only the lookup
    // function's erased universe, preserving all runtime arguments, its meta
    // check, and the EXACT original source type passed to the lookup. This is
    // an unsafe Reference-oracle adapter, never production Rust or a cast of
    // the target value to a different source telescope. The pin-original IR
    // positive below must pass through this same adapter before native IR.
    let (adapter, evaluation) = if probe.higher_universe {
        (
            "universe u\nprivate unsafe def evalConstAt :\n    (α : Type u) -> Lean.Environment -> Lean.Options -> Lean.Name -> Bool -> Except String α :=\n  unsafeCast (@Lean.Environment.evalConst)\n",
            format!(
                "evalConstAt ({}) env {{}} `{} {}",
                probe.ty, probe.entry, probe.check_meta,
            ),
        )
    } else {
        (
            "",
            format!(
                "env.evalConst ({}) {{}} `{} (checkMeta := {})",
                probe.ty, probe.entry, probe.check_meta,
            ),
        )
    };
    let mut source = format!(
        "import Lean\n{adapter}unsafe def main : IO Unit := do\n  Lean.enableInitializersExecution\n  let env ← Lean.importModules #[{{ module := `NativeIrCase, isMeta := true }}] {{}} (loadExts := true)\n  match {evaluation} with\n  | .error message => throw (IO.userError message)\n  | .ok compiled => do\n    IO.println (reprStr ({}))\n    IO.println (reprStr ({}))\n",
        probe.application, probe.application,
    );
    if let Some(call) = probe.heap_call {
        source.push_str(&format!("    let saved ← IO.FS.readFile \"heap-input.txt\"\n    let got := {call}\n    IO.println (reprStr (got, saved))\n"));
    }
    let filename = format!("Runtime-{label}.lean");
    std::fs::write(dir.join(&filename), source).unwrap();
    Command::new(lean)
        .current_dir(dir)
        .env("LEAN_PATH", dir)
        .args(["-j", "1", "--run", &filename])
        .output()
        .unwrap()
}

fn assert_probe(output: std::process::Output, dir: &Path, label: &str, expected: &str) {
    std::fs::write(dir.join(format!("{label}.stdout")), &output.stdout).unwrap();
    std::fs::write(dir.join(format!("{label}.stderr")), &output.stderr).unwrap();
    assert!(
        output.status.success(),
        "{label}: {:?}: {} {}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout).unwrap().trim(),
        expected,
        "{label}"
    );
}

fn consume_enum_ir(
    lean: &Path,
    dir: &Path,
    label: &str,
    ty: &str,
    application: &str,
    entry: &str,
) -> std::process::Output {
    // Import the enum declarations for typechecking this consumer, but obtain
    // the target value dynamically. No reference to the logical compiled
    // constant can substitute its body for the executable under test.
    let source = format!(
        "import Lean\nimport NativeIrCase\nunsafe def main : IO Unit := do\n  Lean.enableInitializersExecution\n  let env ← Lean.importModules #[{{ module := `NativeIrCase, isMeta := true }}] {{}} (loadExts := true)\n  match env.evalConst ({ty}) {{}} `{entry} (checkMeta := false) with\n  | .error message => throw (IO.userError message)\n  | .ok compiled => do\n    IO.println (reprStr ({application}))\n    IO.println (reprStr ({application}))\n",
    );
    let filename = format!("EnumRuntime-{label}.lean");
    std::fs::write(dir.join(&filename), source).unwrap();
    Command::new(lean)
        .current_dir(dir)
        .env("LEAN_PATH", dir)
        .args(["-j", "1", "--run", &filename])
        .output()
        .unwrap()
}

#[test]
fn the_pin_executes_fieldless_enum_exports_and_observes_their_tags() {
    let Some(lean) = reference() else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference is required"
        );
        eprintln!("SKIP: native enum IR compilation consumer requires the pin");
        return;
    };
    let pin = include_str!("../../../SUITE.lock")
        .lines()
        .find(|line| line.starts_with("reference "))
        .unwrap()
        .split_whitespace()
        .find_map(|field| field.strip_prefix("commit="))
        .unwrap();
    let identity = Command::new(&lean).arg("--githash").output().unwrap();
    assert!(identity.status.success());
    assert_eq!(String::from_utf8(identity.stdout).unwrap().trim(), pin);
    let base = enum_base();
    let options = KVMap::new();
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    for (index, case) in enum_export_cases().into_iter().enumerate() {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir = root.join(format!(
            "native-enum-ir-{}-{unique}-{index}",
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let source = format!("def compiled : {} := {}", case.ty, case.body);
        let (declaration, _) = checked_definition(&base, &source);
        let compiled = ir::compile_source_definition(
            &base,
            declaration,
            &options,
            limits(),
            CompileLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .into_complete()
        .unwrap();
        std::fs::write(
            dir.join("NativeIrCase.lean"),
            format!(
                "module\npublic section\n{ENUM_DATA_HELPERS}\nopaque compiled : {} := {}\n",
                case.ty, case.body,
            ),
        )
        .unwrap();
        let generated = Command::new(&lean)
            .current_dir(&dir)
            .args(["-o", "NativeIrCase.olean", "NativeIrCase.lean"])
            .output()
            .unwrap();
        assert_probe(generated, &dir, "compile", "");
        let original = std::fs::read(dir.join("NativeIrCase.ir")).unwrap();
        std::fs::write(dir.join("original.ir"), &original).unwrap();
        let expected = format!("{}\n{}", case.expected, case.expected);
        assert_probe(
            consume_enum_ir(
                &lean,
                &dir,
                "original",
                case.ty,
                case.application,
                "compiled",
            ),
            &dir,
            "original",
            &expected,
        );
        if let Some((ty, application)) = case.reduced {
            assert_probe(
                consume_enum_ir(
                    &lean,
                    &dir,
                    "original-reduced",
                    ty,
                    application,
                    "compiled._redArg",
                ),
                &dir,
                "original-reduced",
                &expected,
            );
        }
        std::fs::write(
            dir.join("NativeIrCase.ir"),
            encode(&compiled.module, &original),
        )
        .unwrap();
        assert_probe(
            consume_enum_ir(&lean, &dir, "native", case.ty, case.application, "compiled"),
            &dir,
            "native",
            &expected,
        );
        if let Some((ty, application)) = case.reduced {
            assert_probe(
                consume_enum_ir(
                    &lean,
                    &dir,
                    "native-reduced",
                    ty,
                    application,
                    "compiled._redArg",
                ),
                &dir,
                "native-reduced",
                &expected,
            );
        }
        if index == 0 {
            // Change only the exported nullary enum tag. The logical opaque
            // and every internal declaration stay byte-for-byte unchanged.
            let mut mutant = compiled.module.clone();
            let IrDecl::Function { body, .. } = mutant
                .decls
                .iter_mut()
                .find(|declaration| declaration.name() == &name("compiled"))
                .unwrap()
            else {
                panic!("enum source entry")
            };
            *body = IrBody {
                stmts: vec![IrStmt::VDecl {
                    x: 1,
                    ty: IrType::UInt8,
                    expr: IrExpr::Lit(IrLit::Num(IrNat::Small(0))),
                }],
                terminal: Box::new(IrTerminal::Ret(IrArg::Var(1))),
            };
            std::fs::write(dir.join("NativeIrCase.ir"), encode(&mutant, &original)).unwrap();
            assert_probe(
                consume_enum_ir(
                    &lean,
                    &dir,
                    "changed-tag",
                    case.ty,
                    case.application,
                    "compiled",
                ),
                &dir,
                "changed-tag",
                "0\n0",
            );
        }
    }
}

fn consume_boxed_ir(
    lean: &Path,
    dir: &Path,
    label: &str,
    ty: &str,
    application: &str,
    entry: &str,
) -> std::process::Output {
    // Heap fields come from IO, so retaining the caller's original value after
    // each call checks ownership of allocated payloads rather than literals.
    // Dynamic lookup also prevents logical bodies from replacing native IR.
    // Validate both inputs even for constant cases, keeping the fixture checks
    // meaningful and avoiding unused-binding warnings in the runtime stdout.
    let source = format!(
        "import Lean\nimport NativeIrCase\nunsafe def main : IO Unit := do\n  let heap ← IO.FS.readFile \"heap-input.txt\"\n  let digits ← IO.FS.readFile \"heap-nat.txt\"\n  let large := digits.toNat!\n  unless heap == \"boxed heap payload\" do throw (IO.userError \"wrong heap String fixture\")\n  unless large == 184467440737095516160 do throw (IO.userError \"wrong heap Nat fixture\")\n  Lean.enableInitializersExecution\n  let env ← Lean.importModules #[{{ module := `NativeIrCase, isMeta := true }}] {{}} (loadExts := true)\n  match env.evalConst ({ty}) {{}} `{entry} (checkMeta := false) with\n  | .error message => throw (IO.userError message)\n  | .ok compiled => do\n    IO.println (reprStr ({application}))\n    IO.println (reprStr ({application}))\n",
    );
    let filename = format!("BoxedRuntime-{label}.lean");
    std::fs::write(dir.join(&filename), source).unwrap();
    Command::new(lean)
        .current_dir(dir)
        .env("LEAN_PATH", dir)
        .args(["-j", "1", "--run", &filename])
        .output()
        .unwrap()
}

#[test]
fn the_pin_executes_boxed_data_exports_and_observes_payloads() {
    check_pin_boxed_data_exports(boxed_export_cases());
}

#[test]
fn the_pin_executes_recursive_data_exports_and_observes_payloads() {
    check_pin_boxed_data_exports(recursive_export_cases());
}

fn check_pin_boxed_data_exports(cases: Vec<BoxedExportCase>) {
    let Some(lean) = reference() else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference is required"
        );
        eprintln!("SKIP: native boxed-data IR compilation consumer requires the pin");
        return;
    };
    let pin = include_str!("../../../SUITE.lock")
        .lines()
        .find(|line| line.starts_with("reference "))
        .unwrap()
        .split_whitespace()
        .find_map(|field| field.strip_prefix("commit="))
        .unwrap();
    let identity = Command::new(&lean).arg("--githash").output().unwrap();
    assert!(identity.status.success());
    assert_eq!(String::from_utf8(identity.stdout).unwrap().trim(), pin);
    let base = boxed_base();
    let options = KVMap::new();
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    for (index, case) in cases.into_iter().enumerate() {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir = root.join(format!(
            "native-boxed-ir-{}-{unique}-{index}",
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("heap-input.txt"), "boxed heap payload").unwrap();
        std::fs::write(dir.join("heap-nat.txt"), "184467440737095516160").unwrap();
        let source = format!("def compiled : {} := {}", case.ty, case.body);
        let (declaration, _) = checked_definition(&base, &source);
        let compiled = ir::compile_source_definition(
            &base,
            declaration,
            &options,
            limits(),
            CompileLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .into_complete()
        .unwrap();
        std::fs::write(
            dir.join("NativeIrCase.lean"),
            format!(
                "module\npublic section\n{INTERNAL_DATA_HELPERS}\n{ENUM_DATA_HELPERS}\n{BOXED_DATA_HELPERS}\nopaque compiled : {} := {}\n",
                case.ty, case.body,
            ),
        )
        .unwrap();
        let generated = Command::new(&lean)
            .current_dir(&dir)
            .args(["-o", "NativeIrCase.olean", "NativeIrCase.lean"])
            .output()
            .unwrap();
        assert_probe(generated, &dir, "compile", "");
        let original = std::fs::read(dir.join("NativeIrCase.ir")).unwrap();
        std::fs::write(dir.join("original.ir"), &original).unwrap();
        let expected = format!("{}\n{}", case.expected, case.expected);
        for (label, bytes) in [
            ("original", original.clone()),
            ("native", encode(&compiled.module, &original)),
        ] {
            std::fs::write(dir.join("NativeIrCase.ir"), bytes).unwrap();
            assert_probe(
                consume_boxed_ir(&lean, &dir, label, case.ty, case.application, "compiled"),
                &dir,
                label,
                &expected,
            );
            if let Some((ty, application)) = case.reduced {
                let label = format!("{label}-reduced");
                assert_probe(
                    consume_boxed_ir(&lean, &dir, &label, ty, application, "compiled._redArg"),
                    &dir,
                    &label,
                    &expected,
                );
            }
        }
        if index == 0 && case.ty == "IRBoxedRecord" {
            let mut mutant = compiled.module.clone();
            let IrDecl::Function { body, .. } = mutant
                .decls
                .iter_mut()
                .find(|declaration| declaration.name() == &name("compiled"))
                .unwrap()
            else {
                panic!("boxed source entry")
            };
            *body = IrBody {
                stmts: vec![
                    IrStmt::VDecl {
                        x: 1,
                        ty: IrType::TObject,
                        expr: IrExpr::Lit(IrLit::Num(IrNat::Small(99))),
                    },
                    IrStmt::VDecl {
                        x: 2,
                        ty: IrType::Object,
                        expr: IrExpr::Lit(IrLit::Str("changed payload".into())),
                    },
                    IrStmt::VDecl {
                        x: 3,
                        ty: IrType::Object,
                        expr: IrExpr::Ctor {
                            info: fln_olean::ir::IrCtorInfo {
                                name: name("IRBoxedRecord.mk"),
                                cidx: 0,
                                size: 2,
                                usize: 0,
                                ssize: 0,
                            },
                            args: vec![IrArg::Var(1), IrArg::Var(2)],
                        },
                    },
                ],
                terminal: Box::new(IrTerminal::Ret(IrArg::Var(3))),
            };
            std::fs::write(dir.join("NativeIrCase.ir"), encode(&mutant, &original)).unwrap();
            assert_probe(
                consume_boxed_ir(
                    &lean,
                    &dir,
                    "changed-payload",
                    case.ty,
                    case.application,
                    "compiled",
                ),
                &dir,
                "changed-payload",
                "(99, \"changed payload\")\n(99, \"changed payload\")",
            );
        }
        if case.ty == "IRRecursive" {
            // Keep the logical declaration fixed and change only its native
            // executable body. The recursive consumer must observe the empty
            // constructor instead of reconstructing the source-level chain.
            let mut mutant = compiled.module.clone();
            let IrDecl::Function { body, .. } = mutant
                .decls
                .iter_mut()
                .find(|declaration| declaration.name() == &name("compiled"))
                .unwrap()
            else {
                panic!("recursive source entry")
            };
            *body = IrBody {
                stmts: vec![IrStmt::VDecl {
                    x: 1,
                    ty: IrType::TObject,
                    expr: IrExpr::Lit(IrLit::Num(IrNat::Small(0))),
                }],
                terminal: Box::new(IrTerminal::Ret(IrArg::Var(1))),
            };
            std::fs::write(dir.join("NativeIrCase.ir"), encode(&mutant, &original)).unwrap();
            assert_probe(
                consume_boxed_ir(
                    &lean,
                    &dir,
                    "changed-recursive-tag",
                    case.ty,
                    case.application,
                    "compiled",
                ),
                &dir,
                "changed-recursive-tag",
                "0\n0",
            );
        }
        if case.ty == "IRScalarBox" {
            // Change only the Boolean payload. This consumer must read the
            // packed byte from native IR, not the companion logical body.
            let mut mutant = compiled.module.clone();
            let IrDecl::Function { body, .. } = mutant
                .decls
                .iter_mut()
                .find(|declaration| declaration.name() == &name("compiled"))
                .unwrap()
            else {
                panic!("scalar source entry")
            };
            *body = IrBody {
                stmts: vec![
                    IrStmt::VDecl {
                        x: 1,
                        ty: IrType::TObject,
                        expr: IrExpr::Lit(IrLit::Num(IrNat::Small(42))),
                    },
                    IrStmt::VDecl {
                        x: 2,
                        ty: IrType::UInt8,
                        expr: IrExpr::Lit(IrLit::Num(IrNat::Small(0))),
                    },
                    IrStmt::VDecl {
                        x: 3,
                        ty: IrType::Object,
                        expr: IrExpr::Ctor {
                            info: fln_olean::ir::IrCtorInfo {
                                name: name("IRScalarBox.mk"),
                                cidx: 0,
                                size: 1,
                                usize: 0,
                                ssize: 1,
                            },
                            args: vec![IrArg::Var(1)],
                        },
                    },
                    IrStmt::SSet {
                        x: 3,
                        i: 1,
                        offset: 0,
                        y: 2,
                        ty: IrType::UInt8,
                    },
                ],
                terminal: Box::new(IrTerminal::Ret(IrArg::Var(3))),
            };
            std::fs::write(dir.join("NativeIrCase.ir"), encode(&mutant, &original)).unwrap();
            assert_probe(
                consume_boxed_ir(
                    &lean,
                    &dir,
                    "changed-scalar",
                    case.ty,
                    case.application,
                    "compiled",
                ),
                &dir,
                "changed-scalar",
                "(42, false)\n(42, false)",
            );
        }
        if case.ty == "IRNatWrapper" {
            // A wrapper is the underlying Nat, not a one-slot allocation.
            // Alter only native IR so the pin must observe this representation
            // instead of evaluating the unchanged logical constructor body.
            let mut mutant = compiled.module.clone();
            let IrDecl::Function { body, .. } = mutant
                .decls
                .iter_mut()
                .find(|declaration| declaration.name() == &name("compiled"))
                .unwrap()
            else {
                panic!("unboxed wrapper source entry")
            };
            *body = IrBody {
                stmts: vec![IrStmt::VDecl {
                    x: 1,
                    ty: IrType::TObject,
                    expr: IrExpr::Lit(IrLit::Num(IrNat::Small(99))),
                }],
                terminal: Box::new(IrTerminal::Ret(IrArg::Var(1))),
            };
            std::fs::write(dir.join("NativeIrCase.ir"), encode(&mutant, &original)).unwrap();
            assert_probe(
                consume_boxed_ir(
                    &lean,
                    &dir,
                    "changed-wrapper",
                    case.ty,
                    case.application,
                    "compiled",
                ),
                &dir,
                "changed-wrapper",
                "99\n99",
            );
        }
    }
}

fn reduced_case(index: usize) -> Option<(&'static str, &'static str)> {
    match index {
        7 | 11 => Some(("Nat -> Nat", "compiled 184467440737095516160")),
        10 => Some(("Nat -> Nat", "compiled 42")),
        12 => Some(("String -> String", "compiled \"retained string\"")),
        19 => Some(("String -> String", "compiled \"erased type string\"")),
        13 | 16 => Some(("Nat -> Nat", "compiled 42")),
        15 | 21 => Some(("Nat -> Nat", "compiled 184467440737095516160")),
        22 => Some((
            "(Nat -> String) -> Nat -> String",
            "compiled (fun _ => \"typed callback\") 7",
        )),
        28 => Some(("Nat -> Nat", "compiled 42")),
        29 | 31 | 34 => Some(("Bool -> Bool", "compiled true")),
        32 => Some(("String -> String", "compiled \"retained Boolean string\"")),
        51 => Some(("Bool -> String", "compiled false")),
        _ => None,
    }
}

#[test]
fn the_pin_executes_native_compiler_output_and_observes_changed_bodies() {
    let Some(lean) = reference() else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference is required"
        );
        eprintln!("SKIP: native IR compilation consumer requires the pin");
        return;
    };
    let pin = include_str!("../../../SUITE.lock")
        .lines()
        .find(|s| s.starts_with("reference "))
        .unwrap()
        .split_whitespace()
        .find_map(|s| s.strip_prefix("commit="))
        .unwrap();
    let identity = Command::new(&lean).arg("--githash").output().unwrap();
    assert!(identity.status.success());
    assert_eq!(String::from_utf8(identity.stdout).unwrap().trim(), pin);
    let base = base();
    let options = KVMap::new();
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    for (index, (ty, expression, expected)) in cases()
        .into_iter()
        .chain([
            ("String", "\"aliased borrow\"", "\"aliased borrow\""),
            ("String", "\"aliased borrow\"", "\"aliased borrow\""),
            ("String", "\"cached closure\"", "\"cached closure\""),
        ])
        .enumerate()
    {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir = root.join(format!(
            "native-ir-compiler-{}-{unique}-{index}",
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let source = format!("def generated : {ty} := {expression}");
        let run = base
            .execute_source_definitions(&[source.as_bytes()], &options, limits())
            .unwrap()
            .into_complete()
            .unwrap();
        let mut compiled = ir::compile_definition(
            &base,
            run.executions[0].declaration.clone(),
            &name("compiled"),
            &options,
            limits(),
            CompileLimits::default(),
        )
        .unwrap_or_else(|e| panic!("{source}: {e:?}"))
        .into_complete()
        .unwrap();
        if index >= cases().len() {
            // These final three are lower-level FIR compiler controls, not
            // claims that this FIR was derived from the source declaration.
            let program = if index == cases().len() + 2 {
                cached_closure_program()
            } else {
                aliased_borrow_program(index == cases().len() + 1)
            };
            let lowered =
                fln_comp::fir::lower_to_flbc_with_ownership(&program, Default::default()).unwrap();
            let bytes =
                fln_comp::flbc::encode_canonical(lowered.program(), Default::default()).unwrap();
            let execution = fln::execute_flbc_artifact(&bytes, &options, Default::default())
                .unwrap()
                .into_complete()
                .unwrap();
            let VmExit::Returned(value) = execution else {
                panic!("valid aliased-borrow FIR must execute")
            };
            let view = value.value.try_string_view().unwrap();
            assert_eq!(
                view.3[..view.0 - 1],
                expected.trim_matches('"').as_bytes()[..]
            );
            compiled.module =
                ir::compile(&program, &name("compiled"), CompileLimits::default()).unwrap();
        }
        // The oracle supplies the logical companions only. Its IR bodies are
        // retained as a control and never supplied to the native compiler.
        std::fs::write(
            dir.join("NativeIrCase.lean"),
            format!("module\n{HELPERS}\npublic opaque compiled : {ty} := {expression}\n"),
        )
        .unwrap();
        let generated = Command::new(&lean)
            .current_dir(&dir)
            .args(["-o", "NativeIrCase.olean", "NativeIrCase.lean"])
            .output()
            .unwrap();
        std::fs::write(dir.join("compile.stdout"), &generated.stdout).unwrap();
        std::fs::write(dir.join("compile.stderr"), &generated.stderr).unwrap();
        assert!(
            generated.status.success(),
            "{}{}",
            String::from_utf8_lossy(&generated.stdout),
            String::from_utf8_lossy(&generated.stderr)
        );
        let original = std::fs::read(dir.join("NativeIrCase.ir")).unwrap();
        std::fs::write(dir.join("original.ir"), &original).unwrap();
        let bytes = encode(&compiled.module, &original);
        std::fs::write(dir.join("NativeIrCase.ir"), &bytes).unwrap();
        std::fs::write(
            dir.join("Consumer.lean"),
            "module\nmeta import NativeIrCase\n#eval compiled\n",
        )
        .unwrap();
        let result = consume(&lean, &dir);
        std::fs::write(dir.join("native.stdout"), &result.stdout).unwrap();
        std::fs::write(dir.join("native.stderr"), &result.stderr).unwrap();
        assert!(
            result.status.success(),
            "{source} in {} ({:?}): {}{}",
            dir.display(),
            result.status,
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(
            String::from_utf8(result.stdout).unwrap().trim(),
            expected,
            "{source}"
        );
        let mut mutant = compiled.module.clone();
        let target = mutant
            .decls
            .iter_mut()
            .find(|d| d.name() == &name("compiled"))
            .unwrap();
        let IrDecl::Function { body, .. } = target else {
            panic!("entry is a function")
        };
        let (ir_type, literal, wanted) = if ty == "Nat" {
            (IrType::Tagged, IrLit::Num(IrNat::Small(99)), "99")
        } else {
            (
                IrType::Object,
                IrLit::Str("changed IR".into()),
                "\"changed IR\"",
            )
        };
        *body = IrBody {
            stmts: vec![IrStmt::VDecl {
                x: 1,
                ty: ir_type,
                expr: IrExpr::Lit(literal),
            }],
            terminal: Box::new(IrTerminal::Ret(IrArg::Var(1))),
        };
        std::fs::write(dir.join("NativeIrCase.ir"), encode(&mutant, &original)).unwrap();
        let changed = consume(&lean, &dir);
        std::fs::write(dir.join("mutant.stdout"), &changed.stdout).unwrap();
        std::fs::write(dir.join("mutant.stderr"), &changed.stderr).unwrap();
        assert!(changed.status.success());
        assert_eq!(String::from_utf8(changed.stdout).unwrap().trim(), wanted);
        if expression.contains("invoke") {
            // Keep the root unchanged: the Reference must reach a callback
            // application emitted by this backend, rather than an unused one.
            let mut mutant = compiled.module.clone();
            let mut changed_functions = 0;
            for declaration in &mut mutant.decls {
                let IrDecl::Function { params, body, .. } = declaration else {
                    continue;
                };
                if !body.stmts.iter().any(|stmt| {
                    matches!(
                        stmt,
                        IrStmt::VDecl {
                            expr: IrExpr::Ap { .. },
                            ..
                        }
                    )
                }) {
                    continue;
                }
                changed_functions += 1;
                replace_result(params, body, ty);
            }
            assert!(changed_functions > 0);
            std::fs::write(dir.join("NativeIrCase.ir"), encode(&mutant, &original)).unwrap();
            let changed = consume(&lean, &dir);
            std::fs::write(dir.join("callback-mutant.stdout"), &changed.stdout).unwrap();
            std::fs::write(dir.join("callback-mutant.stderr"), &changed.stderr).unwrap();
            assert!(changed.status.success());
            assert_eq!(String::from_utf8(changed.stdout).unwrap().trim(), wanted);
        }
        // Change only boxed entry bodies. A PAP aimed at the borrowing base
        // would ignore this control and leak the operands it is given to own.
        let mut mutant = compiled.module.clone();
        let mut boxed_entries = 0;
        for declaration in &mut mutant.decls {
            let IrDecl::Function {
                name, params, body, ..
            } = declaration
            else {
                continue;
            };
            if name.to_display_string().ends_with("._boxed") {
                replace_result(params, body, ty);
                boxed_entries += 1;
            }
        }
        if expression.contains("invoke") || index >= cases().len() {
            assert!(
                boxed_entries > 0,
                "the boxed-entry control must not be vacuous"
            );
            std::fs::write(dir.join("NativeIrCase.ir"), encode(&mutant, &original)).unwrap();
            let changed = consume(&lean, &dir);
            std::fs::write(dir.join("boxed-mutant.stdout"), &changed.stdout).unwrap();
            std::fs::write(dir.join("boxed-mutant.stderr"), &changed.stderr).unwrap();
            assert!(
                changed.status.success(),
                "boxed mutant: {:?}",
                changed.status
            );
            assert_eq!(String::from_utf8(changed.stdout).unwrap().trim(), wanted);
        }
        std::fs::write(dir.join("NativeIrCase.ir"), bytes).unwrap();
    }
}

#[test]
fn the_pin_executes_imported_string_source_exports() {
    check_pin_string_exports(false);
}

#[test]
fn the_pin_executes_multiargument_calls_and_reduced_let_exports() {
    let Some(lean) = reference() else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference is required"
        );
        eprintln!("SKIP: multiargument source IR exports require the pin");
        return;
    };
    let pin = include_str!("../../../SUITE.lock")
        .lines()
        .find(|line| line.starts_with("reference "))
        .unwrap()
        .split_whitespace()
        .find_map(|field| field.strip_prefix("commit="))
        .unwrap();
    let identity = Command::new(&lean).arg("--githash").output().unwrap();
    assert!(identity.status.success());
    assert_eq!(String::from_utf8(identity.stdout).unwrap().trim(), pin);
    let stack = 256 * 1024 * 1024;
    std::thread::Builder::new()
        .stack_size(stack)
        .spawn(move || {
            // This producer uses the checked native source seed, as the other
            // source-export differential tests do. The pin supplies the real
            // runtime/consumer and independent original/reduced signatures.
            // Imported String model admission has its separate tests below.
            let base = base();
            let options = KVMap::new();
            let original_root = base.logical_root(&options);
            let mut no_execution = EngineExecutionLimits::new(Budget::for_stack_bytes(stack));
            no_execution.vm.max_steps = 0;
            let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
                .map(PathBuf::from)
                .unwrap_or_else(std::env::temp_dir);
            for (index, case) in native_call_export_cases().into_iter().enumerate() {
                let source = format!("def compiled : {} := {}", case.ty, case.expression);
                let (declaration, checked) = checked_definition(&base, &source);
                let compiled = ir::compile_source_definition(
                    &base,
                    declaration,
                    &options,
                    no_execution,
                    CompileLimits::default(),
                )
                .unwrap_or_else(|error| panic!("{source}: {error:?}"))
                .into_complete()
                .unwrap();
                assert_definition_admission(&base, &checked, &compiled, &options);
                assert_eq!(base.logical_root(&options), original_root);
                let unique = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos();
                let dir = root.join(format!(
                    "native-multiargument-export-{}-{unique}-{index}",
                    std::process::id()
                ));
                std::fs::create_dir_all(&dir).unwrap();
                std::fs::write(
                    dir.join("NativeIrCase.lean"),
                    format!(
                        "module\npublic opaque compiled : {} := {}\n",
                        case.ty, case.expression
                    ),
                )
                .unwrap();
                let produced = Command::new(&lean)
                    .current_dir(&dir)
                    .args(["-j", "1", "-o", "NativeIrCase.olean", "NativeIrCase.lean"])
                    .output()
                    .unwrap();
                std::fs::write(dir.join("compile.stdout"), &produced.stdout).unwrap();
                std::fs::write(dir.join("compile.stderr"), &produced.stderr).unwrap();
                assert!(
                    produced.status.success(),
                    "{source}: {} {}",
                    String::from_utf8_lossy(&produced.stdout),
                    String::from_utf8_lossy(&produced.stderr)
                );
                let original = std::fs::read(dir.join("NativeIrCase.ir")).unwrap();
                std::fs::write(dir.join("original.ir"), &original).unwrap();
                let bytes = encode(&compiled.module, &original);
                let expected = format!("{}\n{}", case.expected, case.expected);
                let mut probes = vec![
                    RuntimeProbe {
                        ty: case.ty,
                        application: case.application,
                        entry: "compiled",
                        check_meta: true,
                        higher_universe: false,
                        heap_call: None,
                    },
                    RuntimeProbe {
                        ty: case.ty,
                        application: case.partial,
                        entry: "compiled",
                        check_meta: true,
                        higher_universe: false,
                        heap_call: None,
                    },
                ];
                if let Some((ty, application)) = case.reduced {
                    probes.push(RuntimeProbe {
                        ty,
                        application,
                        entry: "compiled._redArg",
                        check_meta: false,
                        higher_universe: false,
                        heap_call: None,
                    });
                }
                for (producer, product) in [
                    ("reference", original.as_slice()),
                    ("native", bytes.as_slice()),
                ] {
                    std::fs::write(dir.join("NativeIrCase.ir"), product).unwrap();
                    for (probe_index, probe) in probes.iter().enumerate() {
                        let label = format!("{producer}-{probe_index}");
                        assert_probe(
                            consume_ir(&lean, &dir, &label, probe),
                            &dir,
                            &label,
                            &expected,
                        );
                    }
                    if index == 9 {
                        std::fs::write(dir.join("heap-input.txt"), "fresh λ😀").unwrap();
                        let probe = RuntimeProbe {
                            ty: case.ty,
                            application: case.application,
                            entry: "compiled",
                            check_meta: true,
                            higher_universe: false,
                            heap_call: Some("(let f := compiled saved; f saved)"),
                        };
                        let label = format!("{producer}-heap-alias");
                        assert_probe(
                            consume_ir(&lean, &dir, &label, &probe),
                            &dir,
                            &label,
                            &format!("{expected}\n(\"fresh λ😀fresh λ😀\", \"fresh λ😀\")"),
                        );
                    }
                }
                std::fs::write(
                    dir.join("Consumer.lean"),
                    format!(
                        "module\nmeta import NativeIrCase\n#eval ({})\n#eval ({})\n",
                        case.application, case.partial,
                    ),
                )
                .unwrap();
                assert_probe(consume(&lean, &dir), &dir, "compiled-consumer", &expected);
                if index == 0 {
                    // Identical logical companions, changed physical source
                    // entry: both full and partially applied runtime lookups
                    // must observe native IR rather than an inlined oracle body.
                    let mut mutant = compiled.module.clone();
                    let IrDecl::Function { params, body, .. } = mutant
                        .decls
                        .iter_mut()
                        .find(|decl| decl.name() == &name("compiled"))
                        .unwrap()
                    else {
                        panic!("source entry")
                    };
                    replace_result(params, body, "Nat");
                    std::fs::write(dir.join("NativeIrCase.ir"), encode(&mutant, &original))
                        .unwrap();
                    for (probe_index, probe) in probes.iter().enumerate() {
                        let label = format!("changed-body-{probe_index}");
                        assert_probe(
                            consume_ir(&lean, &dir, &label, probe),
                            &dir,
                            &label,
                            "99\n99",
                        );
                    }
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn the_pin_executes_consuming_string_predicate_exports() {
    check_pin_string_exports(true);
}

fn check_pin_string_exports(consuming_predicates: bool) {
    let Some(lean) = reference() else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference is required"
        );
        eprintln!("SKIP: imported String IR exports require the pin");
        return;
    };
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .unwrap_or_else(|| lean.parent().unwrap().parent().unwrap().join("lib/lean"));
    assert!(lib.is_dir(), "the pinned Reference library is required");
    let pin = include_str!("../../../SUITE.lock")
        .lines()
        .find(|s| s.starts_with("reference "))
        .unwrap()
        .split_whitespace()
        .find_map(|s| s.strip_prefix("commit="))
        .unwrap();
    let identity = Command::new(&lean).arg("--githash").output().unwrap();
    assert!(identity.status.success());
    assert_eq!(String::from_utf8(identity.stdout).unwrap().trim(), pin);

    // Import the real checked String declarations, including their extern
    // journal and private/server companions. A name-shaped fixture is not
    // sufficient authority for these source intrinsics.
    let stack = 256 * 1024 * 1024;
    std::thread::Builder::new()
        .stack_size(stack)
        .spawn(move || {
            // Check each primitive against its actual producer world. The
            // consuming predicates belong to Bootstrap and do not require
            // Length's unrelated proof-library dependency closure.
            let module_root = if consuming_predicates {
                "Init.Data.String.Bootstrap"
            } else {
                "Init.Data.String.Length"
            };
            let base = imported_strings(&lib, stack, module_root);
            let options = KVMap::new();
            let original_root = base.logical_root(&options);
            let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
                .map(PathBuf::from)
                .unwrap_or_else(std::env::temp_dir);
            struct Case {
                native: &'static str,
                ty: &'static str,
                expression: &'static str,
                application: &'static str,
                expected: &'static str,
                heap_expected: &'static str,
            }
            for case in [
                Case {
                    native: "String.length",
                    ty: "String -> Nat",
                    expression: "fun s => String.length s",
                    application: "(compiled \"\", compiled \"é😀a\", compiled \"é\")",
                    expected: "(0, 3, 2)",
                    heap_expected: "(8, \"fresh λ😀\")",
                },
                Case {
                    native: "String.Internal.length",
                    ty: "String -> Nat",
                    expression: "fun s => String.Internal.length s",
                    application: "(compiled \"\", compiled \"é😀a\", compiled \"é\")",
                    expected: "(0, 3, 2)",
                    heap_expected: "(8, \"fresh λ😀\")",
                },
                Case {
                    native: "String.utf8ByteSize",
                    ty: "String -> Nat",
                    expression: "fun s => String.utf8ByteSize s",
                    application: "(compiled \"\", compiled \"é😀a\", compiled \"é\")",
                    expected: "(0, 7, 3)",
                    heap_expected: "(12, \"fresh λ😀\")",
                },
                Case {
                    native: "String.Internal.append",
                    ty: "String -> String",
                    expression: "fun s => String.Internal.append s s",
                    application: "(compiled \"\", compiled \"é😀a\", compiled \"é\")",
                    expected: "(\"\", \"é😀aé😀a\", \"éé\")",
                    heap_expected: "(\"fresh λ😀fresh λ😀\", \"fresh λ😀\")",
                },
                Case {
                    native: "String.append",
                    ty: "String -> String",
                    expression: "fun s => String.append s s",
                    application: "(compiled \"\", compiled \"é😀a\", compiled \"é\")",
                    expected: "(\"\", \"é😀aé😀a\", \"éé\")",
                    heap_expected: "(\"fresh λ😀fresh λ😀\", \"fresh λ😀\")",
                },
                Case {
                    native: "String.decEq",
                    ty: "String -> Bool",
                    expression: "fun s => decide (s = \"fresh λ😀\")",
                    application: "(compiled \"\", compiled \"fresh λ😀\", compiled \"fresh λ😃\")",
                    expected: "(false, true, false)",
                    heap_expected: "(true, \"fresh λ😀\")",
                },
                Case {
                    native: "String.Internal.isEmpty",
                    ty: "String -> Bool",
                    expression: "fun s => String.Internal.isEmpty s",
                    application: "(compiled \"\", compiled \"é😀a\", compiled \"é\")",
                    expected: "(true, false, false)",
                    heap_expected: "(false, \"fresh λ😀\")",
                },
                Case {
                    native: "String.Internal.isPrefixOf",
                    ty: "String -> Bool",
                    expression: "fun s => String.Internal.isPrefixOf \"é\" s",
                    application: "(compiled \"\", compiled \"é😀a\", compiled \"é\")",
                    expected: "(false, true, false)",
                    heap_expected: "(false, \"fresh λ😀\")",
                },
                Case {
                    native: "String.Internal.isPrefixOf",
                    ty: "String -> Bool",
                    expression: "fun s => String.Internal.isPrefixOf s s",
                    application: "(compiled \"\", compiled \"é😀a\", compiled \"é\")",
                    expected: "(true, true, true)",
                    heap_expected: "(true, \"fresh λ😀\")",
                },
                Case {
                    native: "String.Internal.isPrefixOf",
                    ty: "String -> Bool",
                    expression: "fun s => String.Internal.isPrefixOf s \"fresh λ😀\"",
                    application: "(compiled \"\", compiled \"fresh \" , compiled \"fresh λ😃\")",
                    expected: "(true, true, false)",
                    heap_expected: "(true, \"fresh λ😀\")",
                },
            ] {
                if consuming_predicates != matches!(case.native,
                    "String.Internal.isEmpty" | "String.Internal.isPrefixOf")
                {
                    continue;
                }
                let source = format!("def compiled : {} := {}", case.ty, case.expression);
                let (declaration, checked) = checked_definition(&base, &source);
                let mut no_execution = EngineExecutionLimits::new(Budget::for_stack_bytes(stack));
                no_execution.vm.max_steps = 0;
                let compiled = ir::compile_source_definition(
                    &base,
                    declaration,
                    &options,
                    no_execution,
                    CompileLimits::default(),
                )
                .unwrap_or_else(|error| panic!("{source}: {error:?}"))
                .into_complete()
                .unwrap();
                assert_definition_admission(&base, &checked, &compiled, &options);
                assert_eq!(base.logical_root(&options), original_root);
                let native = name(case.native);
                assert!(compiled.module.decls.iter().any(|declaration| {
                    let IrDecl::Function { body, .. } = declaration else { return false };
                    body.bodies().iter().any(|body| body.stmts.iter().any(|stmt| {
                        matches!(stmt, IrStmt::VDecl { expr: IrExpr::Fap { function, .. }, .. } if function == &native)
                    }))
                }), "{} must actually call its native primitive", case.native);

                let unique = std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos();
                let dir = root.join(format!(
                    "native-string-export-{}-{unique}-{}",
                    std::process::id(),
                    case.native,
                ));
                std::fs::create_dir_all(&dir).unwrap();
                std::fs::write(
                    dir.join("NativeIrCase.lean"),
                    format!("module\npublic opaque compiled : {} := {}\n", case.ty, case.expression),
                ).unwrap();
                let generated = Command::new(&lean)
                    .current_dir(&dir)
                    .args(["-j", "1", "-o", "NativeIrCase.olean", "NativeIrCase.lean"])
                    .output()
                    .unwrap();
                std::fs::write(dir.join("compile.stdout"), &generated.stdout).unwrap();
                std::fs::write(dir.join("compile.stderr"), &generated.stderr).unwrap();
                assert!(generated.status.success(), "{source}: {} {}",
                    String::from_utf8_lossy(&generated.stdout),
                    String::from_utf8_lossy(&generated.stderr));
                let original = std::fs::read(dir.join("NativeIrCase.ir")).unwrap();
                std::fs::write(dir.join("original.ir"), &original).unwrap();
                // Heap input and the caller's retained alias exercise native
                // ownership: append mixes consuming and borrowing arguments,
                // while Bootstrap predicates consume both donated aliases.
                // The fresh caller String must remain usable after either call.
                std::fs::write(dir.join("heap-input.txt"), "fresh λ😀").unwrap();
                let probe = RuntimeProbe {
                    ty: case.ty,
                    application: case.application,
                    entry: "compiled",
                    check_meta: true,
                    higher_universe: false,
                    heap_call: Some("compiled saved"),
                };
                let expected = format!("{}\n{}\n{}", case.expected, case.expected, case.heap_expected);
                assert_probe(consume_ir(&lean, &dir, "string", &probe), &dir, "runtime-reference", &expected);
                let bytes = encode(&compiled.module, &original);
                std::fs::write(dir.join("native.ir"), &bytes).unwrap();
                std::fs::write(dir.join("NativeIrCase.ir"), &bytes).unwrap();
                assert_probe(consume_ir(&lean, &dir, "string", &probe), &dir, "runtime-native", &expected);

                if case.native == "String.length" {
                    // Change only the emitted call, retaining identical source
                    // companions. A runtime lookup must observe byte length,
                    // proving it consumed this physical native IR body.
                    let mut mutant = compiled.module.clone();
                    let mut switched = 0;
                    for declaration in &mut mutant.decls {
                        let IrDecl::Function { body, .. } = declaration else { continue };
                        for stmt in &mut body.stmts {
                            if let IrStmt::VDecl { expr: IrExpr::Fap { function, .. }, .. } = stmt
                                && function == &native
                            {
                                *function = name("String.utf8ByteSize");
                                switched += 1;
                            }
                        }
                    }
                    assert!(switched > 0, "the native-call mutation must not be vacuous");
                    std::fs::write(dir.join("NativeIrCase.ir"), encode(&mutant, &original)).unwrap();
                    assert_probe(consume_ir(&lean, &dir, "string", &probe), &dir,
                        "runtime-byte-size-mutant", "(0, 7, 3)\n(0, 7, 3)\n(12, \"fresh λ😀\")");
                    std::fs::write(dir.join("NativeIrCase.ir"), bytes).unwrap();
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn the_pin_calls_native_source_exports_directly_and_as_functions() {
    check_pin_source_exports(0..52);
}

#[test]
fn the_pin_executes_private_source_records_and_retains_their_fields() {
    check_pin_source_exports(52..export_cases().len());
}

fn check_pin_source_exports(case_indices: std::ops::Range<usize>) {
    let Some(lean) = reference() else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference is required"
        );
        eprintln!("SKIP: source export consumer requires the pin");
        return;
    };
    let pin = include_str!("../../../SUITE.lock")
        .lines()
        .find(|s| s.starts_with("reference "))
        .unwrap()
        .split_whitespace()
        .find_map(|s| s.strip_prefix("commit="))
        .unwrap();
    let identity = Command::new(&lean).arg("--githash").output().unwrap();
    assert!(identity.status.success());
    assert_eq!(String::from_utf8(identity.stdout).unwrap().trim(), pin);
    let base = base();
    let options = KVMap::new();
    let original_root = base.logical_root(&options);
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    for (index, (ty, expression, application, result_type, expected, _)) in export_cases()
        .into_iter()
        .enumerate()
        .filter(|(index, _)| case_indices.contains(index))
    {
        let source = format!("def compiled : {ty} := {expression}");
        let (declaration, checked) = checked_definition(&base, &source);
        let mut no_execution = limits();
        no_execution.vm.max_steps = 0;
        let compiled = ir::compile_source_definition(
            &base,
            declaration,
            &options,
            no_execution,
            CompileLimits::default(),
        )
        .unwrap_or_else(|e| panic!("{source}: {e:?}"))
        .into_complete()
        .unwrap();
        assert_definition_admission(&base, &checked, &compiled, &options);
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir = root.join(format!(
            "native-source-export-{}-{unique}-{index}",
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        // Only logical companions and envelope metadata come from the oracle.
        // Its IR declarations are replaced, never supplied to this compiler.
        std::fs::write(
            dir.join("NativeIrCase.lean"),
            format!(
                "module\n{INTERNAL_DATA_HELPERS}\npublic opaque compiled : {ty} := {expression}\n"
            ),
        )
        .unwrap();
        let generated = Command::new(&lean)
            .current_dir(&dir)
            .args(["-o", "NativeIrCase.olean", "NativeIrCase.lean"])
            .output()
            .unwrap();
        std::fs::write(dir.join("compile.stdout"), &generated.stdout).unwrap();
        std::fs::write(dir.join("compile.stderr"), &generated.stderr).unwrap();
        assert!(
            generated.status.success(),
            "{source}: {}",
            String::from_utf8_lossy(&generated.stderr)
        );
        let original = std::fs::read(dir.join("NativeIrCase.ir")).unwrap();
        std::fs::write(dir.join("original.ir"), &original).unwrap();
        let bytes = encode(&compiled.module, &original);
        std::fs::write(dir.join("NativeIrCase.ir"), &bytes).unwrap();
        std::fs::write(dir.join("native.ir"), &bytes).unwrap();
        let mut consumer = format!(
            "module\nmeta import NativeIrCase\n#eval ({application})\n#eval ({application})\n"
        );
        let mut expected_output = format!("{expected}\n{expected}");
        if matches!(index, 4 | 12 | 19 | 32 | 52 | 55) {
            // Effectful input prevents closed-term lifting from making the
            // alias a persistent literal. The caller keeps it across the call.
            std::fs::write(dir.join("heap-input.txt"), "fresh heap string").unwrap();
            let call = if matches!(index, 4 | 52 | 55) {
                "compiled saved"
            } else if index == 12 {
                "compiled 7 saved"
            } else if index == 32 {
                "compiled false saved"
            } else {
                "compiled Nat saved"
            };
            consumer.push_str(&format!("#eval do\n  let saved ← IO.FS.readFile \"heap-input.txt\"\n  let got := {call}\n  pure (got, saved)\n"));
            expected_output.push_str("\n(\"fresh heap string\", \"fresh heap string\")");
        }
        std::fs::write(dir.join("Consumer.lean"), consumer).unwrap();
        let result = consume(&lean, &dir);
        std::fs::write(dir.join("native.stdout"), &result.stdout).unwrap();
        std::fs::write(dir.join("native.stderr"), &result.stderr).unwrap();
        assert!(
            result.status.success(),
            "{source}: {:?}: {} {}",
            result.status,
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
        assert_eq!(
            String::from_utf8(result.stdout).unwrap().trim(),
            expected_output
        );

        let full_probe = RuntimeProbe {
            ty,
            application,
            entry: "compiled",
            check_meta: true,
            higher_universe: matches!(index, 15 | 17 | 19 | 20 | 21 | 22 | 31),
            heap_call: match index {
                4 | 52 | 55 => Some("compiled saved"),
                12 => Some("compiled 7 saved"),
                19 => Some("compiled Nat saved"),
                32 => Some("compiled false saved"),
                _ => None,
            },
        };
        let reduced_probe = reduced_case(index).map(|(ty, application)| RuntimeProbe {
            ty,
            application,
            entry: "compiled._redArg",
            check_meta: false,
            higher_universe: false,
            heap_call: (index == 12 || index == 19 || index == 32).then_some("compiled saved"),
        });
        assert_eq!(
            compiled
                .module
                .decls
                .iter()
                .any(|d| d.name() == &name("compiled._redArg")),
            reduced_probe.is_some(),
            "the independently specified reduced-entry cases must actually exist",
        );
        // Check this evaluator against the pin's own IR with the same logical
        // companions and independently supplied types before judging our IR.
        std::fs::write(dir.join("NativeIrCase.ir"), &original).unwrap();
        assert_probe(
            consume_ir(&lean, &dir, "full", &full_probe),
            &dir,
            "runtime-reference",
            &expected_output,
        );
        if let Some(probe) = &reduced_probe {
            assert_probe(
                consume_ir(&lean, &dir, "reduced", probe),
                &dir,
                "runtime-reduced-reference",
                &expected_output,
            );
        }
        std::fs::write(dir.join("NativeIrCase.ir"), &bytes).unwrap();
        assert_probe(
            consume_ir(&lean, &dir, "full", &full_probe),
            &dir,
            "runtime-native",
            &expected_output,
        );
        if let Some(probe) = &reduced_probe {
            assert_probe(
                consume_ir(&lean, &dir, "reduced", probe),
                &dir,
                "runtime-reduced-native",
                &expected_output,
            );
        }

        // Alter only the source export, retaining every internal value body.
        let mut mutant = compiled.module.clone();
        let public = mutant
            .decls
            .iter_mut()
            .find(|d| d.name() == &name("compiled"))
            .unwrap();
        let IrDecl::Function { params, body, .. } = public else {
            panic!("source function entry")
        };
        if result_type == "Bool" {
            replace_boolean_result(params, body, IrType::UInt8, expected == "false");
        } else {
            replace_result(params, body, result_type);
        }
        assert_eq!(
            mutant
                .decls
                .iter()
                .filter(|d| d.name() != &name("compiled"))
                .collect::<Vec<_>>(),
            compiled
                .module
                .decls
                .iter()
                .filter(|d| d.name() != &name("compiled"))
                .collect::<Vec<_>>(),
        );
        let mutant_bytes = encode(&mutant, &original);
        std::fs::write(dir.join("export-mutant.ir"), &mutant_bytes).unwrap();
        std::fs::write(dir.join("NativeIrCase.ir"), mutant_bytes).unwrap();
        let result = consume(&lean, &dir);
        std::fs::write(dir.join("export-mutant.stdout"), &result.stdout).unwrap();
        std::fs::write(dir.join("export-mutant.stderr"), &result.stderr).unwrap();
        assert!(
            result.status.success(),
            "{source}: {:?}: {} {}",
            result.status,
            String::from_utf8_lossy(&result.stdout),
            String::from_utf8_lossy(&result.stderr)
        );
        let changed = if result_type == "Nat" {
            "99"
        } else if result_type == "Bool" {
            if expected == "true" { "false" } else { "true" }
        } else {
            "\"changed IR\""
        };
        let mut changed_output = format!("{changed}\n{changed}");
        if matches!(index, 4 | 12 | 19 | 32 | 52 | 55) {
            changed_output.push_str("\n(\"changed IR\", \"fresh heap string\")");
        }
        // Ordinary compilation may inline the logical companion's original
        // body. Retain its diagnostic output, but use direct interpreter calls
        // to require observation of this valid, deliberately changed IR.
        assert_probe(
            consume_ir(&lean, &dir, "full", &full_probe),
            &dir,
            "runtime-export-mutant",
            &changed_output,
        );
        if let Some(probe) = &reduced_probe {
            assert_probe(
                consume_ir(&lean, &dir, "reduced", probe),
                &dir,
                "runtime-reduced-mutant",
                &changed_output,
            );
        }
        if result_type == "Bool" && !boolean_positions(index).is_empty() {
            // Preserve the public entry and change only its boxed adapter.
            // Runtime lookup must execute that adapter, not merely an unused
            // wrapper included in the output module.
            let mut mutant = compiled.module.clone();
            let boxed = mutant
                .decls
                .iter_mut()
                .find(|d| d.name() == &name("compiled._boxed"))
                .unwrap();
            let IrDecl::Function { params, body, .. } = boxed else {
                panic!("source boxed function")
            };
            replace_boolean_result(params, body, IrType::Tagged, expected == "false");
            assert_eq!(
                mutant
                    .decls
                    .iter()
                    .filter(|d| d.name() != &name("compiled._boxed"))
                    .collect::<Vec<_>>(),
                compiled
                    .module
                    .decls
                    .iter()
                    .filter(|d| d.name() != &name("compiled._boxed"))
                    .collect::<Vec<_>>(),
            );
            let bytes = encode(&mutant, &original);
            std::fs::write(dir.join("boxed-export-mutant.ir"), &bytes).unwrap();
            std::fs::write(dir.join("NativeIrCase.ir"), &bytes).unwrap();
            assert_probe(
                consume_ir(&lean, &dir, "full", &full_probe),
                &dir,
                "runtime-boxed-export-mutant",
                &changed_output,
            );
        }
        std::fs::write(dir.join("NativeIrCase.ir"), bytes).unwrap();
        assert_eq!(base.logical_root(&options), original_root);
    }
}
