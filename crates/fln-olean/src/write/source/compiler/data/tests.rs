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
inductive WriterBorrowed where | mk (n : @& Nat) (s : String)
inductive WriterScalar where | mk (b : Bool) (n : Nat)
inductive WriterProof where | mk (p : True) (n : Nat)
inductive WriterParam (α : Type) where | mk (value : α)
inductive WriterIndexed : Nat → Type where | zero : WriterIndexed 0
inductive WriterRecursive where | stop | next (tail : WriterRecursive)
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
        .args(["-o", "WriterData.olean", "WriterData.lean"])
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

#[derive(Debug, PartialEq, Eq)]
enum MapValue {
    Nontrivial,
    Type(Expr),
    Constructor {
        name: Name,
        index: usize,
        size: usize,
        fields: Vec<(usize, Expr)>,
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
                        assert!(value.is_scalar());
                        assert_eq!(value.unbox(), 0, "present map entry with Option.none");
                        MapValue::Nontrivial
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
                        assert_eq!(info.ctor_child(4).unbox(), 0, "no packed scalar bytes");
                        let array = value.ctor_child(1);
                        let fields = (0..array.array_view().0)
                            .map(|index| {
                                let field = array.array_child(index);
                                assert_eq!(field.obj_tag(), 1, "CtorFieldInfo.object");
                                assert_eq!(field.header().other, 2);
                                (
                                    field.ctor_child(0).unbox(),
                                    expression(&mut conversion, &mut heap, &field.ctor_child(1)),
                                )
                            })
                            .collect();
                        MapValue::Constructor {
                            name: ctor_name,
                            index: info.ctor_child(1).unbox(),
                            size: info.ctor_child(2).unbox(),
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
) -> Vec<u8> {
    let header = OleanWriteHeader {
        version: 2,
        flags: 1,
        lean_version: format::PIN_TAG.strip_prefix('v').unwrap(),
        githash: format::PIN_COMMIT,
        base_addr: 2 * format::REGION_ALIGN as u64,
    };
    let mut encoder = Encoder::new(WriteBudget::default(), header.version).unwrap();
    let blocks = encoder.compiler_data_blocks(data).unwrap();
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
) {
    // These are the actual strict pin readers, not a second Rust decoder.
    // No cached state is shared between invocations. The fixture's logical
    // declarations came from the pin; the complete compiler caches below are
    // replaced with newly constructed native bytes before each invocation.
    let reader = r#"import Lean
import WriterData
open Lean Elab Command Compiler LCNF
run_cmd liftCoreM do
  for n in [``WriterEnum, ``WriterSingleton, ``WriterMixed, ``WriterRecord, ``WriterHeap, ``WriterBinders] do
    unless (← hasTrivialStructure? n).isNone do throwError "wrong mono trivial cache"
    unless (← hasTrivialImpureStructure? n).isNone do throwError "wrong impure trivial cache"
    unless (← getOtherDeclMonoType n) == mkConst `lcErased do throwError "wrong mono type"
    let ty ← nameToImpureType n
    let expected := if n == ``WriterEnum then `UInt8
      else if n == ``WriterSingleton then `tagged
      else if n == ``WriterMixed || n == ``WriterBinders then `tobj else `obj
    unless ty == mkConst expected do throwError "wrong impure carrier"
    let .inductInfo iv ← getConstInfo n | throwError "missing type"
    for c in iv.ctors do
      let _ ← getOtherDeclMonoType c
      let layout ← getCtorLayout c
      unless layout.ctorInfo.name == c do throwError "wrong constructor owner"
      unless layout.ctorInfo.size == layout.fieldInfo.size do throwError "wrong field count"
  logInfo "native-data-caches-ok"
"#;
    std::fs::write(directory.join("Reader.lean"), reader).unwrap();
    let run = |bytes: Vec<u8>| {
        std::fs::write(directory.join("WriterData.olean"), bytes).unwrap();
        Command::new(lean)
            .current_dir(directory)
            .env("LEAN_PATH", directory)
            .arg("Reader.lean")
            .output()
            .unwrap()
    };
    let positive = run(native_module(constants, imports, data));
    assert!(
        positive.status.success(),
        "native compiler-cache reader: {}\n{}",
        String::from_utf8_lossy(&positive.stdout),
        String::from_utf8_lossy(&positive.stderr)
    );
    assert!(String::from_utf8_lossy(&positive.stdout).contains("native-data-caches-ok"));
    // Rebuild a coherent graph without WriterMixed's cache rows. Do not build
    // then discard encoded objects: the writer's complete region audit must
    // still account for every allocation in these counterfactual artifacts.
    let absent: Vec<_> = data
        .iter()
        .filter(|row| row.name != name("WriterMixed"))
        .cloned()
        .collect();
    let missing_bytes = native_module(constants, imports, &absent);
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
    let altered = run(native_module(constants, imports, &altered));
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
    assert_live_readers(&lean, &directory, &constants, &module.imports, &data);
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
