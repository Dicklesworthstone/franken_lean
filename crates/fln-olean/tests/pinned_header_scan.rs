//! Every `.olean` part of the pinned stdlib passes the header pin check (bead
//! `fln-fur.1`). Header-only: 88 bytes of each part are read; nothing is decoded.
#![forbid(unsafe_code)]
use fln_olean::format::{OLEAN_HEADER_SIZE, PIN_TAG};
use fln_olean::pin::check_pinned_header;
use std::io::Read;
use std::path::{Path, PathBuf};

fn pinned_lib() -> Option<PathBuf> {
    let lib = std::env::var_os("HOME")
        .map(PathBuf::from)
        .map(|home| {
            home.join(".elan/toolchains")
                .join(format!("leanprover--lean4---{PIN_TAG}"))
                .join("lib/lean")
        })
        .filter(|lib| lib.join("Init/Prelude.olean").is_file());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "FLN_REQUIRE_REFERENCE is set but the pinned Reference lib/lean is absent"
    );
    lib
}

fn parts(directory: &Path, found: &mut Vec<PathBuf>) {
    let mut entries: Vec<_> = std::fs::read_dir(directory)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect();
    entries.sort();
    for path in entries {
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        if path.is_dir() {
            parts(&path, found);
        } else if [".olean", ".olean.server", ".olean.private"]
            .iter()
            .any(|suffix| name.ends_with(suffix))
        {
            found.push(path);
        }
    }
}

#[test]
fn every_pinned_stdlib_part_carries_the_pinned_header() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent");
        return;
    };
    let mut found = Vec::new();
    parts(&lib, &mut found);
    let count = |suffix: &str| {
        found
            .iter()
            .filter(|path| path.to_string_lossy().ends_with(suffix))
            .count()
    };
    let exported = count(".olean");
    let server = count(".olean.server");
    let private = count(".olean.private");
    eprintln!("pinned parts: {exported} .olean, {server} .olean.server, {private} .olean.private");
    // The populations measured at the pin (v4.32.0); a different count means a
    // different library, not a passing scan.
    assert_eq!((exported, server, private), (2433, 2431, 2431));
    let mut refused = Vec::new();
    for path in &found {
        let mut header = vec![0u8; OLEAN_HEADER_SIZE];
        std::fs::File::open(path)
            .unwrap()
            .read_exact(&mut header)
            .unwrap();
        if let Err(mismatch) = check_pinned_header(&header) {
            refused.push(format!("{}: {mismatch}", path.display()));
        }
    }
    assert!(
        refused.is_empty(),
        "{} refused: {refused:#?}",
        refused.len()
    );
}

/// Every pinned part passes the full-surface audit the decoders run, including the
/// compactor's `capacity == size` law for arrays, scalar arrays and strings (bead
/// `fln-fur.1`). Reads all 1.7 GB of the pinned stdlib's parts, so it is ignored by
/// default: `cargo test --release -p fln-olean --test pinned_header_scan -- --ignored`.
#[test]
#[ignore]
fn every_pinned_stdlib_part_passes_the_full_surface_audit() {
    use fln_olean::region::OleanView;
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent");
        return;
    };
    let mut found = Vec::new();
    parts(&lib, &mut found);
    let mut audited = 0usize;
    let mut objects = 0u64;
    let mut refused = Vec::new();
    for path in found
        .iter()
        .filter(|path| path.to_string_lossy().ends_with(".olean"))
    {
        let exported = std::fs::read(path).unwrap();
        let mut chain = vec![exported];
        for suffix in ["olean.server", "olean.private"] {
            let companion = path.with_extension(suffix);
            if companion.is_file() {
                chain.push(std::fs::read(companion).unwrap());
            }
        }
        for index in 0..chain.len() {
            let earlier: Vec<&[u8]> = chain[..index].iter().map(Vec::as_slice).collect();
            let result = OleanView::parse_with_dependencies(&chain[index], &earlier)
                .and_then(|view| view.shared_audit());
            match result {
                Ok(report) => {
                    audited += 1;
                    objects += report.objects;
                }
                Err(error) => refused.push(format!("{} part {index}: {error}", path.display())),
            }
        }
    }
    eprintln!("audited {audited} parts, {objects} objects");
    assert!(
        refused.is_empty(),
        "{} refused: {refused:#?}",
        refused.len()
    );
    assert_eq!(audited, 2433 + 2431 + 2431);
}

/// Every constant of the pin decodes under the declaration decoder's shape laws,
/// including the payload-structure tag law (bead `fln-fur.1`). The private part is
/// the authoritative constant array where a module has one. Ignored by default:
/// `cargo test --release -p fln-olean --test pinned_header_scan -- --ignored`.
#[test]
#[ignore]
fn every_pinned_constant_decodes_under_the_shape_laws() {
    use fln_olean::decl::DeclDecoder;
    use fln_olean::region::{OleanView, WalkBudget};
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent");
        return;
    };
    let mut found = Vec::new();
    parts(&lib, &mut found);
    let mut modules = 0usize;
    let mut constants = 0usize;
    let mut refused = Vec::new();
    for path in found
        .iter()
        .filter(|path| path.to_string_lossy().ends_with(".olean"))
    {
        let exported = std::fs::read(path).unwrap();
        let server = path.with_extension("olean.server");
        let private = path.with_extension("olean.private");
        let decode = |view: OleanView<'_>| {
            DeclDecoder::new(&view, WalkBudget::default())
                .decode_module_constants()
                .map_err(|error| error.to_string())
        };
        let result = if private.is_file() {
            let server = std::fs::read(server).unwrap();
            let private = std::fs::read(private).unwrap();
            OleanView::parse_with_dependencies(&private, &[&exported, &server])
                .map_err(|error| error.to_string())
                .and_then(decode)
        } else {
            OleanView::parse(&exported)
                .map_err(|error| error.to_string())
                .and_then(decode)
        };
        modules += 1;
        match result {
            Ok(decoded) => constants += decoded.len(),
            Err(error) => refused.push(format!("{}: {error}", path.display())),
        }
    }
    eprintln!("decoded {modules} modules, {constants} constants");
    assert!(
        refused.is_empty(),
        "{} refused: {refused:#?}",
        refused.len()
    );
    assert_eq!(modules, 2433);
}
