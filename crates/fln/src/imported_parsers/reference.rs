//! Exact pinned artifact representations exercise native descriptor reduction.
//! This is a decoded-data compatibility test, not a kernel admission claim:
//! the temporary Environment below contains decoded, unchecked declarations,
//! never becomes an Engine, and never supplies a production import receipt.
//! No Reference executable or imported IR runs in this test.
use super::*;
use crate::{OleanDecodeLimits, decode_olean_module_artifacts};
use fln_olean::region::{OleanView, WalkBudget};
use fln_parse::extensions::Descr;
use std::path::{Path, PathBuf};

fn module_constants(lib: &Path, module: &str) -> Vec<ConstantInfo> {
    let path = lib.join(format!("{}.olean", module.replace('.', "/")));
    let public = std::fs::read(&path).unwrap_or_else(|error| panic!("{path:?}: {error}"));
    let server =
        std::fs::read(path.with_extension("olean.server")).expect("pinned module server companion");
    let private = std::fs::read(path.with_extension("olean.private"))
        .expect("pinned module private companion");
    let decoded = decode_olean_module_artifacts(
        &public,
        &server,
        &private,
        OleanDecodeLimits::new(public.len() + server.len() + private.len()),
    )
    .unwrap_or_else(|error| panic!("{module}: {error}"));
    assert_eq!(decoded.header.githash, fln_olean::format::PIN_COMMIT);
    assert!(decoded.companion_parts_loaded);
    if module == "Init.Prelude" {
        // Prelude defines parser-description data without registering parsers.
        // Preparing its complete journal must preserve the existing imported
        // macro CLI path whose artifact closure contains only this Prelude.
        let view = OleanView::parse_with_dependencies(&private, &[&public, &server]).unwrap();
        let blocks = view
            .extension_payloads(WalkBudget::default(), 32 << 20)
            .unwrap();
        let journal = parsers::decode(&blocks, DecodeLimits::default()).unwrap();
        assert!(
            journal.is_empty(),
            "Init.Prelude parser journal: {journal:?}"
        );
        eprintln!("actual Init.Prelude parser journal is empty");
    }
    decoded.constants
}

#[test]
fn installed_conv_descriptions_reconstruct_actual_constructor_values_without_execution() {
    let Some(lib) = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference artifacts required for descriptor reconstruction"
        );
        eprintln!("SKIP: actual descriptor representation requires FLN_REFERENCE_LIB");
        return;
    };
    // Prelude supplies the real datatype interfaces, literal Name helpers and
    // Nat numeral projection. Conv supplies these four simple descriptions.
    // This deliberately does not load or claim to admit the Init closure.
    let mut environment = Environment::new();
    for module in ["Init.Prelude", "Init.Conv"] {
        for declaration in module_constants(&lib, module) {
            environment = environment.add_decl(declaration).unwrap();
        }
    }
    let allowed: BTreeSet<_> = environment
        .constants()
        .map(|(name, _)| name.clone())
        .collect();
    let mut reader = data::Reader::new(
        &environment,
        &allowed,
        data::DataLimits {
            max_steps: 100_000,
            max_depth: 64,
            max_bytes: 16_384,
        },
    );
    let mut nodes = 64;
    let module = name("Init.Conv");
    for symbol in ["skip", "cbv", "lhs", "rhs"] {
        let declaration = Name::str(name("Lean.Parser.Tactic.Conv"), symbol);
        let owner = environment.find(&declaration).unwrap();
        let (leading, value) = description_body(&module, &declaration, owner)
            .unwrap_or_else(|error| panic!("{error}"));
        assert!(leading);
        let descr = descriptions::read(
            &mut reader,
            value,
            &environment,
            &module,
            &declaration,
            &mut nodes,
            64,
        )
        .unwrap_or_else(|error| panic!("{error}"));
        // src/Init/Conv.lean declares these atom-like entries in category conv
        // with behavior Both: maximum precedence and a nonreserved first atom.
        assert_eq!(
            descr,
            Descr::Node {
                kind: declaration,
                prec: 1024,
                body: Box::new(Descr::NonReservedSymbol(symbol.into(), false)),
            }
        );
    }
    assert!(reader.used().contains(&name("Lean.ParserDescr.node")));
    assert!(
        reader.used().contains(&name("Lean.ParserDescr.sepBy1")),
        "all generated constructor interfaces are validated, even unused variants"
    );
    assert!(reader.used().contains(&name("Lean.Name.str")));
    eprintln!("actual Init.Conv ParserDescr values reconstructed: skip, cbv, lhs, rhs");
}
