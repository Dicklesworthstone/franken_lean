//! The independent String and file adapters must coexist in one VM program.
use super::*;

fn mixed_environment() -> Option<Environment> {
    let mut environment = raw_bytes_environment()?;
    let library = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB").unwrap());
    // Actual comparison data supplies the remainder of the String/UTF-8
    // closure. Source candidates still pass both ordinary checkers; this is
    // not admission of the imported module graph.
    for module in [
        "Init/Prelude",
        "Init/Core",
        "Init/Data/List/Basic",
        "Init/Data/ByteArray/Bootstrap",
        "Init/Data/String/Defs",
        "Init/SimpLemmas",
        "Init/Data/ByteArray/Lemmas",
        "Init/Data/Char/Basic",
        "Init/Data/Repr",
    ] {
        let path = library.join(module).with_extension("olean");
        let parts = [
            std::fs::read(&path).unwrap(),
            std::fs::read(path.with_extension("olean.server")).unwrap(),
            std::fs::read(path.with_extension("olean.private")).unwrap(),
        ];
        let decoded = decode_olean_module_artifacts(
            &parts[0],
            &parts[1],
            &parts[2],
            OleanDecodeLimits::new(STACK),
        )
        .unwrap();
        for constant in decoded.constants {
            if !environment.contains(constant.name()) {
                environment = environment.add_decl(constant).unwrap();
            }
        }
        if module != "Init/Prelude" {
            continue;
        }
        // The full imported world selects these genuine native arithmetic
        // contracts. Retaining only the file externs leaves the actual slow
        // recursive companions selected while constructing even a short
        // Unicode String, before the combined IO action can be tested.
        let view = if decoded.module.is_module {
            fln_olean::region::OleanView::parse_with_dependencies(
                &parts[2],
                &[parts[0].as_slice(), parts[1].as_slice()],
            )
        } else {
            fln_olean::region::OleanView::parse(&parts[0])
        }
        .unwrap();
        let blocks = view
            .extension_payloads(OleanWalkBudget::default(), STACK)
            .unwrap();
        let metadata = metadata::decode(&blocks, metadata::DecodeLimits::default()).unwrap();
        let wanted = [
            "Nat.add", "Nat.sub", "Nat.mul", "Nat.pow", "Nat.pred", "Nat.beq", "Nat.ble",
            "Nat.div", "Nat.mod",
        ]
        .map(name);
        let mut retained = std::collections::BTreeSet::new();
        for row in metadata
            .externs
            .into_iter()
            .filter(|row| wanted.contains(&row.declaration))
        {
            assert!(retained.insert(row.declaration.clone()));
            let entries = row
                .entries
                .into_iter()
                .map(|entry| match entry {
                    metadata::ExternEntry::Adhoc { backend } => {
                        fln_elab::externs::ExternEntry::Adhoc { backend }
                    }
                    metadata::ExternEntry::Inline { backend, pattern } => {
                        fln_elab::externs::ExternEntry::Inline { backend, pattern }
                    }
                    metadata::ExternEntry::Standard { backend, symbol } => {
                        fln_elab::externs::ExternEntry::Standard { backend, symbol }
                    }
                    metadata::ExternEntry::Opaque => fln_elab::externs::ExternEntry::Opaque,
                })
                .collect();
            environment =
                fln_elab::externs::register(&environment, &row.declaration, entries).unwrap();
        }
        assert_eq!(retained, wanted.into_iter().collect());
    }
    let environment = write_environment(&environment, None);
    Some(helper_extern(&environment, "String.ofByteArray", false))
}

#[test]
fn checked_string_construction_and_binary_writes_share_native_rows_and_replay() {
    let Some(environment) = mixed_environment() else {
        return;
    };
    let engine = Engine::from_environment(environment);
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let directory = directory("string-and-byte-writes");
    let output = directory.join("mixed.bin");
    let source = format!(
        r#"def text : String := String.ofByteArray (List.utf8Encode ['λ', '\x00']) (ByteArray.IsValidUTF8.intro ['λ', '\x00'] rfl)
#eval do
  let h ← IO.FS.Handle.mk {} IO.FS.Mode.write
  h.putStr text
  h.write ({SOURCE_BYTES})"#,
        quoted(&output)
    );
    let batch = run(&engine, &source);
    let execution = evaluation(&batch);
    assert_unit(&execution.exit);
    let program = assert_rows(
        execution,
        &[Operation::Open, Operation::PutStr, Operation::Write],
    );
    for row in [
        "extern:String.ofByteArray",
        "extern:ByteArray.emptyWithCapacity",
        "extern:ByteArray.push",
        "extern:UInt8.ofBitVec",
    ] {
        assert!(
            program.functions().iter().flat_map(|function| &function.code).any(
                |instruction| matches!(instruction, Instruction::Intrinsic { row: used, .. } if used == row)
            ),
            "the combined program retains {row}"
        );
    }
    let expected: Vec<_> = "λ\0".as_bytes().iter().chain(EXPECTED).copied().collect();
    assert_eq!(std::fs::read(&output).unwrap(), expected);
    assert_eq!(
        flbc::encode_canonical(&program, Default::default()).unwrap(),
        execution.flbc_artifact
    );
    // Replay reconstructs both independently owned buffers and repeats the
    // actual effects, including truncation, rather than returning old output.
    std::fs::write(&output, b"stale bytes that must be replaced").unwrap();
    let replay = execute_golem_with_options(&program, &options, VmExecutionLimits::default())
        .into_complete()
        .unwrap();
    assert_unit(&replay);
    assert_eq!(std::fs::read(&output).unwrap(), expected);
    assert_eq!(engine.logical_root(&options), root);
}
