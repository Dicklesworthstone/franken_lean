//! Ground payload layouts cross one canonical ABI row per reference operation.
use super::*;
use fln_rt::obj::Obj;

fn source() -> String {
    let declarations = r#"
structure StoredPayload where
  number : Nat
  label : String

structure PayloadReport where
  natBefore : Nat
  natOld : Nat
  natNow : Nat
  textBefore : String
  textOld : String
  textNow : String
  listBefore : List Nat
  listOld : List Nat
  listNow : List Nat
  recordBefore : StoredPayload
  recordOld : StoredPayload
  recordNow : StoredPayload
"#;
    // A linear source description keeps every binding named and makes the
    // intended sequence reviewable. The generated term is ordinary ST.bind.
    let stages = [
        ("numbers", "ST.Prim.mkRef (σ := sigma) (α := Nat) 1"),
        (
            "texts",
            "ST.Prim.mkRef (σ := sigma) (α := String) \"kept λ\"",
        ),
        (
            "lists",
            "ST.Prim.mkRef (σ := sigma) (α := List Nat) (List.cons 2 List.nil)",
        ),
        (
            "records",
            "ST.Prim.mkRef (σ := sigma) (α := StoredPayload) (StoredPayload.mk 20 \"record before\")",
        ),
        ("natBefore", "ST.Prim.Ref.get numbers"),
        ("let readText", "ST.Prim.Ref.get texts"),
        ("textBefore", "readText"),
        ("listBefore", "ST.Prim.Ref.get lists"),
        ("recordBefore", "ST.Prim.Ref.get records"),
        ("_", "ST.Prim.Ref.set numbers 2"),
        ("_", "ST.Prim.Ref.set texts \"middle β\""),
        ("_", "ST.Prim.Ref.set lists (List.cons 3 List.nil)"),
        (
            "_",
            "ST.Prim.Ref.set records (StoredPayload.mk 21 \"record middle\")",
        ),
        ("natOld", "ST.Prim.Ref.swap numbers 3"),
        ("textOld", "ST.Prim.Ref.swap texts \"final 🙂\""),
        ("listOld", "ST.Prim.Ref.swap lists (List.cons 4 List.nil)"),
        (
            "recordOld",
            "ST.Prim.Ref.swap records (StoredPayload.mk 22 \"record final\")",
        ),
        ("natNow", "ST.Prim.Ref.get numbers"),
        ("textNow", "readText"),
        ("listNow", "ST.Prim.Ref.get lists"),
        ("recordNow", "ST.Prim.Ref.get records"),
    ];
    let mut term = "ST.pure (PayloadReport.mk natBefore natOld natNow textBefore textOld textNow listBefore listOld listNow recordBefore recordOld recordNow)".to_owned();
    for (binder, action) in stages.into_iter().rev() {
        term = if let Some(local) = binder.strip_prefix("let ") {
            format!("let {local} := {action}; {term}")
        } else {
            format!("ST.bind ({action}) (fun {binder} => {term})")
        };
    }
    format!(
        "{declarations}\ndef mixedPayloadReport : PayloadReport := runST (fun sigma => {term})\n#eval PayloadReport.natNow mixedPayloadReport\n{}",
        r#"
#eval let initial := ST.Prim.mkRef (σ := Unit) (α := String) "direct" (Void.mk (σ := Unit) Unit.unit);
  let result := ST.Prim.Ref.get (ST.Out.val initial) (ST.Out.state initial);
  ST.Out.val result

#eval runST (fun sigma =>
  let allocate := ST.Prim.mkRef (σ := sigma) (α := String) "shared initializer"
  ST.bind allocate (fun first =>
    ST.bind allocate (fun second =>
      ST.bind (ST.Prim.Ref.set first "changed") (fun _ =>
        ST.Prim.Ref.get second))))
"#
    )
}

fn nat(value: &Obj, expected: usize) {
    assert!(value.is_scalar(), "expected scalar {expected}");
    assert_eq!(value.unbox(), expected);
}

fn text(value: &Obj, expected: &str) {
    let (size, _, _, bytes) = value.try_string_view().expect("native string payload");
    assert_eq!(&bytes[..size - 1], expected.as_bytes());
}

fn field(value: &Obj, index: usize) -> Obj {
    value
        .try_ctor_child(index)
        .unwrap_or_else(|| panic!("missing field {index}"))
}

fn returned(execution: &DefinitionExecution) -> &Obj {
    assert_eq!(execution.checker.schema, "fln.checker-admission/1");
    assert_eq!(
        execution.checker.ground,
        CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
    );
    let fln::VmExit::Returned(returned) = &execution.exit else {
        panic!("payload execution did not return: {:?}", execution.exit)
    };
    &returned.value
}

fn report(execution: &DefinitionExecution) {
    let value = returned(execution);
    for (index, expected) in [1, 2, 3].into_iter().enumerate() {
        nat(&field(value, index), expected);
    }
    for (index, expected) in ["kept λ", "middle β", "final 🙂"].into_iter().enumerate() {
        text(&field(value, index + 3), expected);
    }
    for (index, expected) in [2, 3, 4].into_iter().enumerate() {
        let list = field(value, index + 6);
        assert_eq!(list.obj_tag(), 1);
        nat(&field(&list, 0), expected);
        assert_eq!(field(&list, 1).obj_tag(), 0);
    }
    for (index, (number, label)) in [
        (20, "record before"),
        (21, "record middle"),
        (22, "record final"),
    ]
    .into_iter()
    .enumerate()
    {
        let record = field(value, index + 9);
        nat(&field(&record, 0), number);
        text(&field(&record, 1), label);
    }
    // Each instruction encodes its row ID, so repeated calls legitimately
    // repeat that string. Across all payload families the only distinct IDs
    // must be the four canonical generated rows; FIR also rejects duplicate
    // catalog entries for one row before this artifact can be produced.
    let program = fln_comp::flbc::decode_canonical(
        &execution.flbc_artifact,
        fln_comp::flbc::CodecLimits::default(),
    )
    .unwrap();
    let rows: std::collections::BTreeSet<_> = program
        .functions()
        .iter()
        .flat_map(|function| &function.code)
        .filter_map(|instruction| match instruction {
            fln_comp::flbc::Instruction::Intrinsic { row, .. } => Some(row.clone()),
            _ => None,
        })
        .collect();
    assert_eq!(
        rows,
        EXTERNS[1..]
            .iter()
            .map(|(target, _)| format!("extern:{target}"))
            .collect()
    );
}

pub(super) fn check_payloads(engine: &Engine) {
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
    let program = source();
    let run = || {
        engine
            .execute_source_commands_with_checks(program.as_bytes(), &options, limits)
            .unwrap()
            .into_complete()
            .unwrap()
    };
    let first = run();
    assert_eq!(first.batch.source_evaluation_indices.len(), 3);
    // The aggregate is a checked definition, not a #eval of a record lacking
    // Repr. Its ordinary scalar projection is also valid in the pinned Lean.
    assert!(matches!(
        &first.batch.executions[0].declaration,
        Declaration::Defn(definition) if definition.base.name == name("mixedPayloadReport")
    ));
    report(&first.batch.executions[0]);
    let executions: Vec<_> = first
        .batch
        .source_evaluation_indices
        .iter()
        .map(|&index| &first.batch.executions[index])
        .collect();
    assert_scalar(executions[0], 3);
    text(returned(executions[1]), "direct");
    text(returned(executions[2]), "shared initializer");
    let query = executions[1].declaration.clone();
    let artifacts: Vec<_> = first
        .batch
        .executions
        .iter()
        .map(|value| value.flbc_artifact.clone())
        .collect();
    drop(executions);
    drop(first);
    let repeated = run();
    for (execution, bytes) in repeated.batch.executions.iter().zip(artifacts) {
        assert_eq!(execution.flbc_artifact, bytes);
    }
    report(&repeated.batch.executions[0]);
    drop(repeated);
    assert_eq!(engine.logical_root(&options), root);

    for reserved in ["_fln_runtime_st_payload", "_fln_runtime_st_ref"] {
        let source = format!("def {reserved} : Nat := 0\n");
        let collision = engine
            .check_source_files(
                &[source.as_bytes()],
                &options,
                SourceCheckLimits::new(limits.admission()),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
        assert!(matches!(
            rejected(&collision, &query, limits),
            EngineExecutionError::Ingress(IngressError::UnsupportedNode {
                kind: "ST runtime carrier name collision"
            })
        ));
    }
    // A completed function interface is not part of the ground-data slice.
    // In particular, a previously used canonical New row cannot authorize it.
    let unsupported = r#"
def unsupportedCell : Nat := runST (fun sigma =>
  ST.bind (ST.Prim.mkRef (σ := sigma) (α := Nat) 0) (fun _ =>
    ST.bind (ST.Prim.mkRef (σ := sigma) (α := Nat -> Nat) (fun n => n))
      (fun _ => ST.pure 0)))
"#;
    let checked = engine
        .check_source_files(
            &[unsupported.as_bytes()],
            &options,
            SourceCheckLimits::new(limits.admission()),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let query = Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name("unsupportedCellQuery"),
            level_params: vec![],
            type_: constant("Nat"),
        },
        value: constant("unsupportedCell"),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name("unsupportedCellQuery")],
    });
    assert!(matches!(
        rejected(&checked, &query, limits),
        EngineExecutionError::Ingress(_)
    ));
    assert_eq!(engine.logical_root(&options), root);
}

#[test]
fn decoded_ground_payloads_share_canonical_rows_without_import_admission() {
    let Some(library) = reference_library() else {
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            check_payloads(&decoded_st_fixture(&library));
        })
        .unwrap()
        .join()
        .unwrap();
}
