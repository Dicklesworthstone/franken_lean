//! Optional retained CLI fixture; this creates a new module, never an IO import receipt.
use super::*;
use std::io::Write;

pub(super) fn retain(
    engine: &Engine,
    selected: &BTreeSet<Name>,
    fixtures: &[Declaration],
    parts: &BTreeMap<Name, Parts>,
    origins: &[(Name, Vec<Name>)],
) {
    let Some(directory) = std::env::var_os("FLN_IO_SELECTED_FIXTURE_DIR").map(PathBuf::from) else {
        return;
    };
    let externs = fln_elab::externs::ExternTable::read(engine.environment()).unwrap();
    for label in selected {
        assert!(
            externs.get(label).is_none(),
            "basic fixture writer cannot silently lose selected extern metadata: {label:?}"
        );
    }
    let mut constants = BTreeMap::new();
    for label in selected {
        constants.insert(
            label.clone(),
            engine.environment().find(label).unwrap().clone(),
        );
    }
    let mut fixture_names = Vec::new();
    for declaration in fixtures {
        let Declaration::Defn(value) = declaration else {
            unreachable!()
        };
        let actual = engine.environment().find(&value.base.name).unwrap();
        assert_eq!(actual, &ConstantInfo::Defn(value.clone()));
        assert!(externs.get(&value.base.name).is_none());
        constants.insert(value.base.name.clone(), actual.clone());
        fixture_names.push(value.base.name.clone());
    }
    let constants: Vec<_> = constants.into_values().collect();
    let imports = [fln::OleanModuleImport {
        module: name("Init.System.ST"),
        import_all: true,
        is_exported: true,
        is_meta: false,
    }];
    let encoded = fln::encode_olean_module(
        fln::OleanModuleWriteInput {
            is_module: false,
            imports: &imports,
            constants: &constants,
            extra_const_names: &[],
        },
        fln::OleanWriteHeader {
            version: fln::OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: fln::OLEAN_PIN_TAG.strip_prefix('v').unwrap(),
            githash: fln::OLEAN_PIN_COMMIT,
            base_addr: 2 * fln::OLEAN_REGION_ALIGN as u64,
        },
        fln::OleanWriteBudget::default(),
    )
    .unwrap();
    let decoded =
        fln::decode_olean_artifact(&encoded.bytes, OleanDecodeLimits::new(BYTES)).unwrap();
    assert_eq!(
        decoded.constants, constants,
        "faithful selected declaration roundtrip"
    );
    assert!(matches!(decoded.independent, IndependentReading::Read(_)));

    use fln_hash::domain::{Domain, hash};
    let mut manifest = format!(
        "schema fln-selected-io-cli-fixture/1\nmodule SelectedIoFixture\n\
         authority selected pinned IO declarations dual-checked over actual admitted ST54; NOT full Init.System.IO module admission\n\
         pin {}\nhash_algorithm BLAKE3 derive_key {:?}\n\
         fixture_bytes {}\nfixture_digest {}\nengine_logical_root {:?}\n",
        fln::OLEAN_PIN_COMMIT,
        Domain::Fixture.tag(),
        encoded.bytes.len(),
        hash(Domain::Fixture, &encoded.bytes),
        engine.logical_root(&KVMap::new()),
    );
    for (module, declarations) in origins {
        let (public, server, private) = &parts[module];
        for (part, bytes) in [
            ("public", Some(public.as_slice())),
            ("server", server.as_deref()),
            ("private", private.as_deref()),
        ] {
            if let Some(bytes) = bytes {
                manifest.push_str(&format!(
                    "source_part {:?} {part} {} {}\n",
                    module,
                    bytes.len(),
                    hash(Domain::Fixture, bytes)
                ));
            }
        }
        for label in declarations {
            manifest.push_str(&format!("selected {:?} from {:?}\n", label, module));
        }
    }
    for label in fixture_names {
        manifest.push_str(&format!("fixture_definition {label:?}\n"));
    }
    // New files only: a repeated run retains the first evidence rather than
    // overwriting its bytes or performing cleanup.
    std::fs::create_dir_all(&directory).unwrap();
    let artifact = directory.join("SelectedIoFixture.olean");
    std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&artifact)
        .unwrap()
        .write_all(&encoded.bytes)
        .unwrap();
    let provenance = directory.join("SelectedIoFixture.provenance.txt");
    std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&provenance)
        .unwrap()
        .write_all(manifest.as_bytes())
        .unwrap();
    eprintln!(
        "Retained honest selected-declaration CLI module: {}",
        artifact.display()
    );
}
