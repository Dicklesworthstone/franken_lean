use super::*;
use crate::decl::DeclDecoder;
use crate::region::{OleanView, OpaqueExtensionBlock, WalkBudget};
use fln_rt::convert::Conversion;
use fln_rt::native_heap::NativeHeap;
use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;
use std::process::Command;

fn name(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn encode(metadata: &SourceMetadata, budget: WriteBudget) -> WResult<EncodedModule> {
    encode_module_with_source_metadata(
        ModuleWriteInput {
            is_module: false,
            imports: &[],
            constants: &[],
            extra_const_names: &[],
        },
        metadata,
        OleanWriteHeader {
            version: 2,
            flags: 1,
            lean_version: format::PIN_TAG.strip_prefix('v').unwrap(),
            githash: format::PIN_COMMIT,
            base_addr: 2 * format::REGION_ALIGN as u64,
        },
        budget,
    )
}

const SOURCE: &str = r#"import Init.Core
inductive WriterEnum where | a | b | c
inductive WriterSingleton where | only
inductive WriterMixed where | empty | text (n : Nat) (s : String)
structure WriterRecord where
  text : String
  size : Nat
inductive WriterHeap where | text (s : String) | number (n : Nat)
inductive WriterBinders where | empty | data {n : Nat} {{s : String}}
inductive WriterWrapper where | mk (n : Nat)
structure WriterStringWrapper where
  value : String
inductive WriterBorrowed where | mk (n : @& Nat) (s : String)
inductive WriterScalar where | mk (b : Bool) (n : Nat)
structure WriterInterleaved where
  first : Bool
  number : Nat
  second : Bool
  text : String
structure WriterAllBools where
  first : Bool
  second : Bool
  third : Bool
inductive WriterScalarSum where | empty | value (b : Bool)
inductive WriterScalarHeap where | bit (b : Bool) | text (s : String)
inductive WriterBoolWrapper where | mk (b : Bool)
inductive WriterWideScalar where | mk (b : UInt32) (n : Nat)
inductive WriterProof where | mk (p : True) (n : Nat)
inductive WriterParam (α : Type) where | mk (value : α)
inductive WriterIndexed : Nat → Type where | zero : WriterIndexed 0
inductive WriterRecursive where | stop | next (tail : WriterRecursive)
inductive WriterRecursiveHeap where
  | leaf (n : Nat) (s : String)
  | node (left : WriterRecursiveHeap) (flag : Bool) (right : WriterRecursiveHeap)
inductive WriterRecursiveFirst where
  | next (tail : WriterRecursiveFirst) (flag : Bool) (n : Nat)
  | stop
inductive WriterRecursiveOnly where | next (tail : WriterRecursiveOnly)
inductive WriterHigherRecursive where | node (children : Nat → WriterHigherRecursive)
inductive WriterProp : Prop where | intro
"#;

fn fixture() -> Option<(PathBuf, PathBuf, Vec<u8>)> {
    let Some(lean) = std::env::var_os("FLN_REFERENCE_LEAN")
        .or_else(|| std::env::var_os("FLN_REFERENCE_BIN"))
        .map(PathBuf::from)
    else {
        assert_ne!(
            std::env::var("FLN_REQUIRE_REFERENCE").as_deref(),
            Ok("1"),
            "this test requires the exact pinned Lean executable"
        );
        eprintln!("skipping actual compiler-data oracle: FLN_REFERENCE_LEAN is unset");
        return None;
    };
    let hash = Command::new(&lean).arg("--githash").output().unwrap();
    assert!(hash.status.success());
    assert_eq!(
        String::from_utf8(hash.stdout).unwrap().trim(),
        format::PIN_COMMIT,
        "compiler-data layouts require the exact pin"
    );
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory =
        std::env::temp_dir().join(format!("fln-compiler-data-{}-{nonce}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(directory.join("WriterData.lean"), SOURCE).unwrap();
    let output = Command::new(&lean)
        .current_dir(&directory)
        .args(["-j", "1", "-o", "WriterData.olean", "WriterData.lean"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "actual pin fixture failed: {}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let bytes = std::fs::read(directory.join("WriterData.olean")).unwrap();
    crate::pin::check_pinned_header(&bytes).unwrap();
    Some((lean, directory, bytes))
}

fn projection(constants: &[ConstantInfo]) -> Vec<CompilerData> {
    constants
        .iter()
        .filter_map(|constant| {
            let ConstantInfo::Induct(inductive) = constant else {
                return None;
            };
            CompilerData::from_inductive(
                inductive,
                |name| constants.iter().find(|constant| constant.name() == name),
                |_| Ok::<_, ()>(()),
            )
            .unwrap()
        })
        .collect()
}

fn closed_family(
    family: &str,
    recursive: bool,
    fields: Vec<Vec<Expr>>,
) -> (InductiveVal, Vec<ConstantInfo>) {
    use fln_env::constants::{ConstantVal, ConstructorVal};

    let family = name(family);
    let constructors: Vec<_> = fields
        .into_iter()
        .enumerate()
        .map(|(index, fields)| {
            let num_fields = fields.len() as u32;
            let ty = fields.into_iter().enumerate().rev().fold(
                Expr::const_(family.clone(), Vec::new()),
                |body, (field, ty)| {
                    Expr::forall_e(
                        Name::num(Name::anonymous(), field as u64),
                        ty,
                        body,
                        BinderInfo::Default,
                    )
                },
            );
            ConstantInfo::Ctor(ConstructorVal {
                base: ConstantVal {
                    name: Name::str(family.clone(), format!("ctor{index}")),
                    level_params: Vec::new(),
                    type_: ty,
                },
                induct: family.clone(),
                cidx: index as u32,
                num_params: 0,
                num_fields,
                is_unsafe: false,
            })
        })
        .collect();
    let inductive = InductiveVal {
        base: ConstantVal {
            name: family.clone(),
            level_params: Vec::new(),
            type_: Expr::sort(Level::one()),
        },
        num_params: 0,
        num_indices: 0,
        all: vec![family],
        ctors: constructors
            .iter()
            .map(|ctor| ctor.name().clone())
            .collect(),
        num_nested: 0,
        is_rec: recursive,
        is_unsafe: false,
        is_reflexive: false,
    };
    (inductive, constructors)
}

fn project_closed(inductive: &InductiveVal, constructors: &[ConstantInfo]) -> Option<CompilerData> {
    CompilerData::from_inductive(
        inductive,
        |name| {
            constructors
                .iter()
                .find(|constructor| constructor.name() == name)
        },
        |_| Ok::<_, ()>(()),
    )
    .unwrap()
}

#[test]
fn recursive_data_uses_the_complete_family_carrier_in_every_self_field() {
    let constant = |value| Expr::const_(name(value), Vec::new());
    for (family, fields, carrier, expected) in [
        (
            "WriterList",
            vec![
                vec![],
                vec![
                    constant("Nat"),
                    constant("WriterList"),
                    constant("Bool"),
                    constant("String"),
                ],
            ],
            IrType::TObject,
            vec![
                vec![],
                vec![
                    IrType::TObject,
                    IrType::TObject,
                    IrType::UInt8,
                    IrType::Object,
                ],
            ],
        ),
        (
            "WriterTree",
            vec![
                vec![constant("Nat"), constant("Bool")],
                vec![
                    constant("WriterTree"),
                    constant("Bool"),
                    constant("WriterTree"),
                ],
            ],
            IrType::Object,
            vec![
                vec![IrType::TObject, IrType::UInt8],
                vec![IrType::Object, IrType::UInt8, IrType::Object],
            ],
        ),
        (
            "WriterLateStop",
            vec![vec![constant("WriterLateStop"), constant("Bool")], vec![]],
            IrType::TObject,
            vec![vec![IrType::TObject, IrType::UInt8], vec![]],
        ),
        (
            "WriterOnlySelf",
            vec![vec![constant("WriterOnlySelf")]],
            IrType::Object,
            vec![vec![IrType::Object]],
        ),
    ] {
        let (inductive, constructors) = closed_family(family, true, fields);
        let projected = project_closed(&inductive, &constructors).unwrap();
        assert!(projected.is_recursive(), "{family}");
        assert!(projected.unboxed_field().is_none(), "{family}");
        assert_eq!(projected.carrier(), &carrier, "{family}");
        assert_eq!(
            projected
                .constructors()
                .map(|(_, fields)| fields.to_vec())
                .collect::<Vec<_>>(),
            expected,
            "{family}",
        );
        // Even the one-constructor, one-self-field family is recursive and
        // cannot acquire the primitive wrapper's reduced constructor result.
        for constructor in &projected.constructors {
            let mut result = &constructor.mono_type;
            while let ExprNode::ForallE { body, .. } = result.node() {
                result = body;
            }
            assert_eq!(result, &constant(family), "{family}");
        }
        // This also walks and encodes the recursive mono types: the projection
        // must not need a recursive object graph or an already compiled cache.
        encode(
            &SourceMetadata {
                compiler_data: vec![projected],
                ..SourceMetadata::default()
            },
            WriteBudget::default(),
        )
        .unwrap();
        assert_eq!(
            CompilerData::from_inductive(
                &inductive,
                |name| constructors.iter().find(|ctor| ctor.name() == name),
                |_| Err("work limit"),
            )
            .unwrap_err(),
            "work limit",
        );
    }
}

#[test]
fn recursive_projection_rejects_special_and_nonuniform_representations() {
    let constant = |value| Expr::const_(name(value), Vec::new());
    for family in ["Nat", "Int", "Lean.Name"] {
        let (inductive, constructors) = closed_family(
            family,
            true,
            vec![
                vec![],
                vec![constant(family), constant("Nat"), constant("String")],
            ],
        );
        assert!(
            project_closed(&inductive, &constructors).is_none(),
            "{family}"
        );
    }
    for (recursive, fields) in [
        (false, vec![vec![], vec![constant("WriterInvalid")]]),
        (true, vec![vec![], vec![constant("Nat")]]),
        (
            true,
            vec![vec![Expr::forall_e(
                name("n"),
                constant("Nat"),
                constant("WriterInvalid"),
                BinderInfo::Default,
            )]],
        ),
        (true, vec![vec![constant("UnrelatedFamily")]]),
    ] {
        let (inductive, constructors) = closed_family("WriterInvalid", recursive, fields);
        assert!(project_closed(&inductive, &constructors).is_none());
    }
    // Recursion does not bypass any of the established closed-family bounds.
    let (inductive, constructors) = closed_family(
        "WriterBounded",
        true,
        vec![vec![], vec![constant("WriterBounded")]],
    );
    for unsupported in [
        InductiveVal {
            num_indices: 1,
            ..inductive.clone()
        },
        InductiveVal {
            num_params: 1,
            ..inductive.clone()
        },
        InductiveVal {
            num_nested: 1,
            ..inductive.clone()
        },
        InductiveVal {
            all: vec![name("WriterBounded"), name("Other")],
            ..inductive.clone()
        },
    ] {
        assert!(project_closed(&unsupported, &constructors).is_none());
    }
}

#[test]
fn compiler_data_rejects_allocator_overflow_even_without_constructor_code() {
    use fln_env::constants::{ConstantVal, ConstructorVal};

    // Identity functions and callbacks need only the signature's data layout;
    // there need not be a constructor instruction for FIR's field bound to see.
    // The shared projection must therefore enforce the physical bound itself.
    for (count, accepted) in [(255, true), (256, false), (257, false)] {
        let family = name("WriterBoundary");
        let constructor = name("WriterBoundary.mk");
        let inductive = InductiveVal {
            base: ConstantVal {
                name: family.clone(),
                level_params: Vec::new(),
                type_: Expr::sort(Level::one()),
            },
            num_params: 0,
            num_indices: 0,
            all: vec![family.clone()],
            ctors: vec![constructor.clone()],
            num_nested: 0,
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        };
        let ty = (0..count)
            .rev()
            .fold(Expr::const_(family.clone(), Vec::new()), |body, index| {
                Expr::forall_e(
                    Name::num(Name::anonymous(), index as u64),
                    Expr::const_(name("Nat"), Vec::new()),
                    body,
                    BinderInfo::Default,
                )
            });
        let constructor = ConstantInfo::Ctor(ConstructorVal {
            base: ConstantVal {
                name: constructor,
                level_params: Vec::new(),
                type_: ty,
            },
            induct: family,
            cidx: 0,
            num_params: 0,
            num_fields: count,
            is_unsafe: false,
        });
        let projected = CompilerData::from_inductive(
            &inductive,
            |name| (name == constructor.name()).then_some(&constructor),
            |_| Ok::<_, ()>(()),
        )
        .unwrap();
        assert_eq!(projected.is_some(), accepted, "{count} object fields");
        if let Some(projected) = projected {
            assert_eq!(projected.carrier(), &IrType::Object);
            assert_eq!(projected.constructors().len(), 1);
            assert_eq!(projected.constructors().next().unwrap().1.len(), 255);
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
enum FieldValue {
    Object {
        index: usize,
        ty: Expr,
    },
    Scalar {
        size: usize,
        offset: usize,
        ty: Expr,
    },
}

#[derive(Debug, PartialEq, Eq)]
enum MapValue {
    Nontrivial,
    Trivial {
        constructor: Name,
        parameters: usize,
        field: usize,
    },
    Type(Expr),
    Constructor {
        name: Name,
        index: usize,
        size: usize,
        scalar_bytes: usize,
        fields: Vec<FieldValue>,
    },
}

fn expression(conversion: &mut Conversion, heap: &mut NativeHeap, value: &Obj) -> Expr {
    let handle = conversion.project_expr(heap, value).unwrap();
    heap.get(handle).unwrap().clone()
}

fn maps(blocks: &[OpaqueExtensionBlock], keep: &BTreeSet<Name>) -> Vec<BTreeMap<Name, MapValue>> {
    let mut conversion = Conversion::new();
    let mut heap = NativeHeap::new();
    extension_names()
        .into_iter()
        .enumerate()
        .map(|(index, key)| {
            let block = blocks
                .iter()
                .find(|block| block.name == key)
                .unwrap_or_else(|| {
                    panic!("missing actual compiler cache {}", key.to_display_string())
                });
            let mut rows = BTreeMap::new();
            let mut previous: Option<Name> = None;
            for bytes in &block.entries {
                let entry = fln_rt::region::materialize(bytes, 0).unwrap();
                assert_eq!(entry.obj_tag(), 0);
                assert_eq!(entry.header().other, 2, "map entries are Name × value");
                let name = conversion.project_name(&entry.ctor_child(0)).unwrap();
                if let Some(previous) = &previous {
                    assert!(previous.quick_cmp(&name).is_lt(), "pin binary-search order");
                }
                previous = Some(name.clone());
                if !keep.contains(&name) {
                    continue;
                }
                let value = entry.ctor_child(1);
                let value = match index {
                    0 | 1 => {
                        if value.is_scalar() {
                            assert_eq!(value.unbox(), layout::OPTION_NONE);
                            MapValue::Nontrivial
                        } else {
                            assert_eq!(value.obj_tag(), usize::from(layout::OPTION_SOME));
                            assert_eq!(value.header().other as usize, layout::OPTION_SOME_POINTERS);
                            let info = value.ctor_child(layout::OPTION_SOME_VAL);
                            assert_eq!(info.obj_tag(), 0);
                            assert_eq!(
                                info.header().other as usize,
                                ir::LCNF_TRIVIAL_STRUCTURE_INFO_POINTERS
                            );
                            MapValue::Trivial {
                                constructor: conversion
                                    .project_name(
                                        &info.ctor_child(ir::LCNF_TRIVIAL_STRUCTURE_INFO_CTOR_NAME),
                                    )
                                    .unwrap(),
                                parameters: info
                                    .ctor_child(ir::LCNF_TRIVIAL_STRUCTURE_INFO_NUM_PARAMS)
                                    .unbox(),
                                field: info
                                    .ctor_child(ir::LCNF_TRIVIAL_STRUCTURE_INFO_FIELD_IDX)
                                    .unbox(),
                            }
                        }
                    }
                    2 | 3 => MapValue::Type(expression(&mut conversion, &mut heap, &value)),
                    4 => {
                        assert_eq!(value.obj_tag(), 0);
                        assert_eq!(value.header().other, 2);
                        let info = value.ctor_child(0);
                        assert_eq!(info.obj_tag(), 0);
                        assert_eq!(info.header().other, 5);
                        let ctor_name = conversion.project_name(&info.ctor_child(0)).unwrap();
                        assert_eq!(info.ctor_child(3).unbox(), 0, "no usize fields");
                        let array = value.ctor_child(1);
                        let fields = (0..array.array_view().0)
                            .map(|index| {
                                let field = array.array_child(index);
                                match field.obj_tag() {
                                    tag if tag == usize::from(ir::LCNF_CTOR_FIELD_OBJECT) => {
                                        assert_eq!(
                                            field.header().other as usize,
                                            ir::LCNF_CTOR_FIELD_OBJECT_POINTERS
                                        );
                                        FieldValue::Object {
                                            index: field
                                                .ctor_child(ir::LCNF_CTOR_FIELD_OBJECT_I)
                                                .unbox(),
                                            ty: expression(
                                                &mut conversion,
                                                &mut heap,
                                                &field.ctor_child(ir::LCNF_CTOR_FIELD_OBJECT_TYPE),
                                            ),
                                        }
                                    }
                                    tag if tag == usize::from(ir::LCNF_CTOR_FIELD_SCALAR) => {
                                        assert_eq!(
                                            field.header().other as usize,
                                            ir::LCNF_CTOR_FIELD_SCALAR_POINTERS
                                        );
                                        FieldValue::Scalar {
                                            size: field
                                                .ctor_child(ir::LCNF_CTOR_FIELD_SCALAR_SZ)
                                                .unbox(),
                                            offset: field
                                                .ctor_child(ir::LCNF_CTOR_FIELD_SCALAR_OFFSET)
                                                .unbox(),
                                            ty: expression(
                                                &mut conversion,
                                                &mut heap,
                                                &field.ctor_child(ir::LCNF_CTOR_FIELD_SCALAR_TYPE),
                                            ),
                                        }
                                    }
                                    tag => panic!("unexpected compiler data field {tag}"),
                                }
                            })
                            .collect();
                        MapValue::Constructor {
                            name: ctor_name,
                            index: info.ctor_child(1).unbox(),
                            size: info.ctor_child(2).unbox(),
                            scalar_bytes: info.ctor_child(4).unbox(),
                            fields,
                        }
                    }
                    _ => unreachable!(),
                };
                assert!(rows.insert(name, value).is_none());
            }
            rows
        })
        .collect()
}

fn native_module(
    constants: &[ConstantInfo],
    imports: &[crate::region::ModuleImport],
    data: &[CompilerData],
    aux_recursors: &[Name],
) -> Vec<u8> {
    let header = OleanWriteHeader {
        version: 2,
        flags: 1,
        lean_version: format::PIN_TAG.strip_prefix('v').unwrap(),
        githash: format::PIN_COMMIT,
        base_addr: 2 * format::REGION_ALIGN as u64,
    };
    let mut encoder = Encoder::new(WriteBudget::default(), header.version).unwrap();
    // The five compiler data maps are rebuilt below. Retain the independent
    // auxiliary-recursor tags of these logical declarations: the pin recognizes
    // an imported `.casesOn` by its tag as well as its name. Without the tag it
    // incorrectly reaches ordinary-call lowering in this stripped fixture and
    // asks for an executable signature that primitive cases do not need.
    let blocks = encoder
        .source_blocks(&SourceMetadata {
            compiler_data: data.to_vec(),
            aux_recursors: aux_recursors.to_vec(),
            ..SourceMetadata::default()
        })
        .unwrap();
    let entries = encoder.array(blocks).unwrap();
    let root = encoder
        .module_root_with_entries(
            ModuleWriteInput {
                is_module: false,
                imports,
                constants,
                extra_const_names: &[],
            },
            Some(entries),
        )
        .unwrap();
    finish_region(
        encoder,
        root,
        build_header(header).unwrap(),
        header.version,
        header.base_addr,
    )
    .unwrap()
    .bytes
}

fn assert_live_readers(
    lean: &std::path::Path,
    directory: &std::path::Path,
    constants: &[ConstantInfo],
    imports: &[crate::region::ModuleImport],
    data: &[CompilerData],
    aux_recursors: &[Name],
) {
    // These are the actual strict pin readers, not a second Rust decoder.
    // No cached state is shared between invocations. The fixture's logical
    // declarations came from the pin; the complete compiler caches below are
    // replaced with newly constructed native bytes before each invocation.
    let reader = r#"import Lean
import WriterData
open Lean Elab Command Compiler LCNF
run_cmd liftCoreM do
  for n in [``WriterEnum, ``WriterSingleton, ``WriterMixed, ``WriterRecord, ``WriterHeap, ``WriterBinders,
      ``WriterScalar, ``WriterInterleaved, ``WriterAllBools, ``WriterScalarSum, ``WriterScalarHeap,
      ``WriterRecursive, ``WriterRecursiveHeap, ``WriterRecursiveFirst, ``WriterRecursiveOnly,
      ``WriterWrapper, ``WriterStringWrapper, ``WriterBoolWrapper] do
    let wrapper := n == ``WriterWrapper || n == ``WriterStringWrapper || n == ``WriterBoolWrapper
    for info? in [(← hasTrivialStructure? n), (← hasTrivialImpureStructure? n)] do
      match info? with
      | none => if wrapper then throwError "missing trivial wrapper cache"
      | some info =>
        unless wrapper && info.ctorName == Name.str n "mk" && info.numParams == 0 && info.fieldIdx == 0 do
          throwError "wrong trivial wrapper cache"
    unless (← getOtherDeclMonoType n) == mkConst `lcErased do throwError "wrong mono type"
    let ty ← nameToImpureType n
    let expected := if n == ``WriterEnum then `UInt8
      else if n == ``WriterSingleton then `tagged
      else if n == ``WriterMixed || n == ``WriterBinders || n == ``WriterScalarSum ||
          n == ``WriterRecursive || n == ``WriterRecursiveFirst then `tobj else `obj
    unless ty == mkConst expected do throwError "wrong impure carrier"
    let publicExpected := if n == ``WriterWrapper then `tobj
      else if n == ``WriterStringWrapper then `obj
      else if n == ``WriterBoolWrapper then `UInt8 else expected
    unless (← toImpureType (mkConst n)) == mkConst publicExpected do
      throwError "wrong public wrapper carrier"
    let .inductInfo iv ← getConstInfo n | throwError "missing type"
    for c in iv.ctors do
      let mono ← getOtherDeclMonoType c
      if wrapper then
        let fieldType := mkConst <| if n == ``WriterWrapper then `Nat
          else if n == ``WriterStringWrapper then `String else `Bool
        let .forallE _ domain result _ := mono | throwError "wrong wrapper constructor mono type"
        unless domain == fieldType && result == fieldType do throwError "unreduced wrapper mono result"
      let layout ← getCtorLayout c
      unless layout.ctorInfo.name == c do throwError "wrong constructor owner"
      let mut objects := 0
      let mut scalarBytes := 0
      for field in layout.fieldInfo do
        match field with
        | .object i _ =>
          unless i == objects do throwError "wrong object index"
          objects := objects + 1
        | .scalar size offset ty =>
          unless size == 1 && offset == scalarBytes && ty == mkConst `UInt8 do
            throwError "wrong packed Bool layout"
          scalarBytes := scalarBytes + size
        | _ => throwError "unexpected field representation"
      unless layout.ctorInfo.size == objects && layout.ctorInfo.usize == 0
          && layout.ctorInfo.ssize == scalarBytes do throwError "wrong field count"
  logInfo "native-data-caches-ok"
def unwrapWriterNat (value : WriterWrapper) : Nat :=
  match value with | .mk n => n
def unwrapWriterString (value : WriterStringWrapper) : String :=
  match value with | .mk s => s
def unwrapWriterBool (value : WriterBoolWrapper) : Bool :=
  match value with | .mk b => b
#eval (unwrapWriterNat (.mk 37), unwrapWriterString (.mk "native wrapper"), unwrapWriterBool (.mk true))
"#;
    std::fs::write(directory.join("Reader.lean"), reader).unwrap();
    let run = |bytes: Vec<u8>| {
        std::fs::write(directory.join("WriterData.olean"), bytes).unwrap();
        Command::new(lean)
            .current_dir(directory)
            .env("LEAN_PATH", directory)
            .args(["-j", "1", "Reader.lean"])
            .output()
            .unwrap()
    };
    let positive = run(native_module(constants, imports, data, aux_recursors));
    assert!(
        positive.status.success(),
        "native compiler-cache reader: {}\n{}",
        String::from_utf8_lossy(&positive.stdout),
        String::from_utf8_lossy(&positive.stderr)
    );
    assert!(String::from_utf8_lossy(&positive.stdout).contains("native-data-caches-ok"));
    assert!(String::from_utf8_lossy(&positive.stdout).contains("(37, \"native wrapper\", true)"));
    // Rebuild a coherent graph without WriterMixed's cache rows. Do not build
    // then discard encoded objects: the writer's complete region audit must
    // still account for every allocation in these counterfactual artifacts.
    let absent: Vec<_> = data
        .iter()
        .filter(|row| row.name != name("WriterMixed"))
        .cloned()
        .collect();
    let missing_bytes = native_module(constants, imports, &absent, aux_recursors);
    for (index, query) in [
        "hasTrivialStructure? ``WriterMixed",
        "hasTrivialImpureStructure? ``WriterMixed",
        "getOtherDeclMonoType ``WriterMixed",
        "nameToImpureType ``WriterMixed",
        "getCtorLayout ``WriterMixed.text",
    ]
    .iter()
    .enumerate()
    {
        std::fs::write(directory.join("Reader.lean"), format!(
            "import Lean\nimport WriterData\nopen Lean Elab Command Compiler LCNF\nrun_cmd liftCoreM do\n  let _ ← {query}\n  logInfo \"unexpected missing-row success\"\n",
        )).unwrap();
        let missing = run(missing_bytes.clone());
        assert!(
            !missing.status.success(),
            "missing compiler map {index} was accepted"
        );
        assert!(
            String::from_utf8_lossy(&missing.stdout).contains("was not compiled"),
            "missing map {index} failed for an unrelated reason: {}\n{}",
            String::from_utf8_lossy(&missing.stdout),
            String::from_utf8_lossy(&missing.stderr)
        );
    }
    let mut altered = data.to_vec();
    altered
        .iter_mut()
        .find(|row| row.name == name("WriterMixed"))
        .unwrap()
        .carrier = IrType::UInt8;
    std::fs::write(directory.join("Reader.lean"), reader).unwrap();
    let altered = run(native_module(constants, imports, &altered, aux_recursors));
    assert!(!altered.status.success());
    assert!(
        String::from_utf8_lossy(&altered.stdout).contains("wrong impure carrier"),
        "changed carrier was not observed: {}\n{}",
        String::from_utf8_lossy(&altered.stdout),
        String::from_utf8_lossy(&altered.stderr)
    );
}

#[test]
fn compiler_data_maps_match_the_actual_pin_and_refuse_unsupported_layouts() {
    let Some((lean, directory, bytes)) = fixture() else {
        return;
    };
    let view = OleanView::parse(&bytes).unwrap();
    let constants = DeclDecoder::new(&view, WalkBudget::default())
        .decode_module_constants()
        .unwrap();
    let data = projection(&constants);
    let actual_names: BTreeSet<_> = data.iter().map(|row| row.name.clone()).collect();
    let expected_names: BTreeSet<_> = [
        "WriterEnum",
        "WriterSingleton",
        "WriterMixed",
        "WriterRecord",
        "WriterHeap",
        "WriterBinders",
        "WriterScalar",
        "WriterInterleaved",
        "WriterAllBools",
        "WriterScalarSum",
        "WriterScalarHeap",
        "WriterRecursive",
        "WriterRecursiveHeap",
        "WriterRecursiveFirst",
        "WriterRecursiveOnly",
        "WriterWrapper",
        "WriterStringWrapper",
        "WriterBoolWrapper",
    ]
    .into_iter()
    .map(name)
    .collect();
    assert_eq!(actual_names, expected_names);
    let keep: BTreeSet<_> = data
        .iter()
        .flat_map(|row| {
            std::iter::once(row.name.clone())
                .chain(row.constructors.iter().map(|ctor| ctor.name.clone()))
        })
        .collect();
    let metadata = SourceMetadata {
        compiler_data: data.clone(),
        ..SourceMetadata::default()
    };
    let encoded = encode(&metadata, WriteBudget::default()).unwrap();
    let native_view = OleanView::parse(&encoded.bytes).unwrap();
    let native = native_view
        .extension_payloads(WalkBudget::default(), 4 * 1024 * 1024)
        .unwrap();
    let actual = view
        .extension_payloads(WalkBudget::default(), 4 * 1024 * 1024)
        .unwrap();
    assert_eq!(maps(&native, &keep), maps(&actual, &keep));
    let module = view.module_data(WalkBudget::default()).unwrap();
    assert!(
        !module.is_module,
        "this wire fixture is a standalone logical module"
    );
    let auxiliary_tags = actual
        .iter()
        .find(|block| block.name == name(layout::AUX_RECURSOR_EXTENSION))
        .unwrap();
    let source_metadata = crate::source_extensions::decode(
        std::slice::from_ref(auxiliary_tags),
        crate::source_extensions::DecodeLimits::default(),
    )
    .unwrap();
    for wrapper in ["WriterWrapper", "WriterStringWrapper", "WriterBoolWrapper"] {
        assert!(
            source_metadata
                .aux_recursors
                .contains(&Name::str(name(wrapper), "casesOn"))
        );
    }
    assert_live_readers(
        &lean,
        &directory,
        &constants,
        &module.imports,
        &data,
        &source_metadata.aux_recursors,
    );
    let ConstantInfo::Induct(inductive) = constants
        .iter()
        .find(|constant| constant.name() == &name("WriterMixed"))
        .unwrap()
    else {
        unreachable!()
    };
    assert!(
        CompilerData::from_inductive(
            inductive,
            |name| constants.iter().find(|constant| constant.name() == name),
            |_| Err("work limit"),
        )
        .is_err(),
        "resource exhaustion is not unsupported-data filtering"
    );
    let duplicate = SourceMetadata {
        compiler_data: vec![data[0].clone(), data[0].clone()],
        ..SourceMetadata::default()
    };
    assert!(matches!(
        encode(&duplicate, WriteBudget::default()),
        Err(WriteError::Contract { .. })
    ));
    assert!(matches!(
        encode(
            &metadata,
            WriteBudget {
                max_objects: 1,
                ..WriteBudget::default()
            }
        ),
        Err(WriteError::Budget { .. })
    ));
}
