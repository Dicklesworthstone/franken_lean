use super::*;
use crate::ir::{IrDecodeLimits, IrExternEntry, decode_ir};
use crate::region::{OleanView, WalkBudget};
use fln_rt::convert::Conversion;
use fln_rt::native_heap::NativeHeap;

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn encode(metadata: &SourceMetadata, budget: WriteBudget) -> WResult<EncodedModule> {
    encode_module_with_source_metadata(
        super::super::tests::input(),
        metadata,
        super::super::tests::header(),
        budget,
    )
}

// The spelling is an independent expectation from LCNF/Types.lean, including
// its synthetic root constants. It is not obtained from the writer's mapping.
fn carriers() -> Vec<(IrType, &'static str)> {
    vec![
        (IrType::Float, "Float"),
        (IrType::Float32, "Float32"),
        (IrType::UInt8, "UInt8"),
        (IrType::UInt16, "UInt16"),
        (IrType::UInt32, "UInt32"),
        (IrType::UInt64, "UInt64"),
        (IrType::USize, "USize"),
        (IrType::Erased, "lcErased"),
        (IrType::Object, "obj"),
        (IrType::TObject, "tobj"),
        (IrType::Tagged, "tagged"),
        (IrType::Void, "lcVoid"),
    ]
}

fn signatures() -> Vec<CompilerSignature> {
    let mut rows: Vec<_> = carriers()
        .into_iter()
        .enumerate()
        .map(|(index, (ty, _))| {
            CompilerSignature::from_ir(
                &IrDecl::Extern {
                    name: Name::num(n("Compiled"), index as u64 + 9),
                    params: vec![
                        IrParam {
                            x: 7,
                            borrow: false,
                            ty: IrType::Erased,
                        },
                        IrParam {
                            x: 19,
                            borrow: true,
                            ty: ty.clone(),
                        },
                    ],
                    result: ty,
                    entries: Vec::new(),
                },
                index % 2 == 0,
            )
        })
        .collect();
    rows.push(CompilerSignature {
        name: n("answer"),
        params: Vec::new(),
        result: IrType::Object,
        safe: false,
    });
    rows
}

fn assert_expr(conversion: &mut Conversion, heap: &mut NativeHeap, obj: &Obj, name: &str) {
    let handle = conversion.project_expr(heap, obj).unwrap();
    assert_eq!(
        heap.get(handle).unwrap(),
        &Expr::const_(n(name), Vec::new())
    );
}

#[test]
fn compiler_signatures_have_pin_record_layout_and_matching_opaque_ir_headers() {
    let rows = signatures();
    let metadata = SourceMetadata {
        compiler_signatures: rows.clone(),
        namespaces: vec![n("Compiled")],
        ..SourceMetadata::default()
    };
    let encoded = encode(&metadata, WriteBudget::default()).unwrap();
    let view = OleanView::parse(&encoded.bytes).unwrap();
    let blocks = view
        .extension_payloads(WalkBudget::default(), 1024 * 1024)
        .unwrap();
    let signature_block = blocks
        .iter()
        .find(|block| block.name == n("Lean.Compiler.LCNF.impureSigExt"))
        .unwrap();
    let mut expected = rows;
    expected.sort_by(|left, right| left.name.quick_cmp(&right.name));
    assert_ne!(expected, metadata.compiler_signatures);
    assert_eq!(signature_block.entries.len(), expected.len());
    let mut conversion = Conversion::new();
    let mut heap = NativeHeap::new();
    for (bytes, signature) in signature_block.entries.iter().zip(&expected) {
        let value = fln_rt::region::materialize(bytes, 0).unwrap();
        // These physical expectations come from the pin's generated Basic.c,
        // independently of the constructor slots used by our writer.
        assert_eq!(value.obj_tag(), 0);
        assert_eq!(value.header().other, 4);
        assert_eq!(
            conversion.project_name(&value.ctor_child(0)).unwrap(),
            signature.name
        );
        assert_eq!(value.ctor_child(1).unbox(), 0, "monomorphic universes");
        let result_name = carriers()
            .into_iter()
            .find(|(ty, _)| *ty == signature.result)
            .unwrap()
            .1;
        assert_expr(
            &mut conversion,
            &mut heap,
            &value.ctor_child(2),
            result_name,
        );
        let params = value.ctor_child(3);
        assert_eq!(params.array_view().0, signature.params.len());
        for (index, param) in signature.params.iter().enumerate() {
            let value = params.array_child(index);
            assert_eq!(value.obj_tag(), 0);
            assert_eq!(value.header().other, 3);
            assert_eq!(
                conversion.project_name(&value.ctor_child(0)).unwrap(),
                Name::num(Name::anonymous(), param.x),
                "FVarId is represented by a raw Name"
            );
            assert_eq!(
                conversion.project_name(&value.ctor_child(1)).unwrap(),
                n("x")
            );
            let type_name = carriers()
                .into_iter()
                .find(|(ty, _)| *ty == param.ty)
                .unwrap()
                .1;
            assert_expr(&mut conversion, &mut heap, &value.ctor_child(2), type_name);
            assert_eq!(
                value.try_ctor_scalar_u64(3 * 8).unwrap().to_le_bytes()[0],
                u8::from(param.borrow)
            );
        }
        assert_eq!(
            value.try_ctor_scalar_u64(4 * 8).unwrap().to_le_bytes()[0],
            u8::from(signature.safe)
        );
    }
    let headers = decode_ir(&blocks, IrDecodeLimits::default()).unwrap();
    let expected_headers: Vec<_> = expected
        .into_iter()
        .map(|signature| IrDecl::Extern {
            name: signature.name,
            params: signature.params,
            result: signature.result,
            entries: vec![IrExternEntry::Opaque],
        })
        .collect();
    assert_eq!(headers.decls, expected_headers);
    assert!(headers.initializers.is_empty());
}

#[test]
fn compiler_metadata_without_namespaces_survives_and_empty_metadata_preserves_basic_bytes() {
    let metadata = SourceMetadata {
        compiler_signatures: vec![CompilerSignature {
            name: n("answer"),
            params: Vec::new(),
            result: IrType::Object,
            safe: false,
        }],
        ..SourceMetadata::default()
    };
    let encoded = encode(&metadata, WriteBudget::default()).unwrap();
    let view = OleanView::parse(&encoded.bytes).unwrap();
    let blocks = view
        .extension_payloads(WalkBudget::default(), 1024 * 1024)
        .unwrap();
    assert_eq!(blocks.len(), 2);
    assert!(
        blocks
            .iter()
            .any(|block| block.name == n("Lean.Compiler.LCNF.impureSigExt"))
    );
    assert_eq!(
        decode_ir(&blocks, IrDecodeLimits::default())
            .unwrap()
            .decls
            .len(),
        1
    );
    let empty = encode(&SourceMetadata::default(), WriteBudget::default()).unwrap();
    let basic = encode_module(
        super::super::tests::input(),
        super::super::tests::header(),
        WriteBudget::default(),
    )
    .unwrap();
    assert_eq!(empty.bytes, basic.bytes);
}

#[test]
fn compiler_metadata_shares_exact_module_byte_and_object_budgets() {
    let metadata = SourceMetadata {
        compiler_signatures: signatures(),
        ..SourceMetadata::default()
    };
    let encoded = encode(&metadata, WriteBudget::default()).unwrap();
    let exact = WriteBudget {
        max_bytes: encoded.report.file_bytes,
        max_objects: encoded.report.runtime_objects,
    };
    assert_eq!(encode(&metadata, exact).unwrap().bytes, encoded.bytes);
    for budget in [
        WriteBudget {
            max_bytes: exact.max_bytes - 1,
            ..exact
        },
        WriteBudget {
            max_objects: exact.max_objects - 1,
            ..exact
        },
    ] {
        assert!(matches!(
            encode(&metadata, budget),
            Err(WriteError::Budget { .. })
        ));
    }
}

#[test]
fn ambiguous_compiler_interfaces_and_unrepresentable_carriers_are_refused() {
    let row = signatures().remove(0);
    let mut anonymous = row.clone();
    anonymous.name = Name::anonymous();
    let mut zero_parameter = row.clone();
    zero_parameter.params[0].x = 0;
    let mut duplicate_parameter = row.clone();
    duplicate_parameter.params[1].x = duplicate_parameter.params[0].x;
    for rows in [
        vec![row.clone(), row.clone()],
        vec![anonymous],
        vec![zero_parameter],
        vec![duplicate_parameter],
    ] {
        let metadata = SourceMetadata {
            compiler_signatures: rows,
            ..SourceMetadata::default()
        };
        assert!(matches!(
            encode(&metadata, WriteBudget::default()),
            Err(WriteError::Contract { .. })
        ));
    }
    for aggregate in [
        IrType::Struct {
            lean_type: None,
            types: vec![IrType::Object],
        },
        IrType::Union {
            lean_type: n("Union"),
            types: vec![IrType::UInt8],
        },
    ] {
        for in_result in [false, true] {
            let mut row = row.clone();
            if in_result {
                row.result = aggregate.clone();
            } else {
                row.params[0].ty = aggregate.clone();
            }
            let metadata = SourceMetadata {
                compiler_signatures: vec![row],
                ..SourceMetadata::default()
            };
            assert!(matches!(
                encode(&metadata, WriteBudget::default()),
                Err(WriteError::Unsupported { .. })
            ));
        }
    }
}
