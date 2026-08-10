//! Exact `.ilean` codec goldens and pinned-Reference corpus round trips.
//!
//! The reviewed golden is immutable during tests: there is no update mode.
//! Candidate changes must be emitted out of band and reviewed byte by byte
//! under the ceremony in `corpus/ILEAN_GOLDEN_PROVENANCE.md`.

#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};

use fln_olean::ilean::{IleanBudget, IleanRefIdent, decode_ilean, encode_ilean};

const GOLDEN_HEX: &str = include_str!("corpus/ilean_probe.hex");
const PROVENANCE: &str = include_str!("corpus/ILEAN_GOLDEN_PROVENANCE.md");
const PIN_COMMIT: &str = "8c9756b28d64dab099da31a4c09229a9e6a2ef35";

fn hex_nibble(byte: u8) -> Result<u8, String> {
    match byte {
        b'0'..=b'9' => Ok(byte - b'0'),
        b'a'..=b'f' => Ok(byte - b'a' + 10),
        b'A'..=b'F' => Ok(byte - b'A' + 10),
        _ => Err(format!("non-hexadecimal fixture byte {byte:#x}")),
    }
}

fn golden_bytes() -> Result<Vec<u8>, String> {
    let hex = GOLDEN_HEX.trim();
    let (pairs, remainder) = hex.as_bytes().as_chunks::<2>();
    if !remainder.is_empty() {
        return Err("ilean golden has an odd number of hexadecimal digits".to_string());
    }
    let mut bytes = Vec::with_capacity(hex.len() / 2);
    for pair in pairs {
        bytes.push((hex_nibble(pair[0])? << 4) | hex_nibble(pair[1])?);
    }
    Ok(bytes)
}

fn first_difference(expected: &[u8], actual: &[u8]) -> String {
    if let Some((offset, (expected, actual))) = expected
        .iter()
        .zip(actual)
        .enumerate()
        .find(|(_, (expected, actual))| expected != actual)
    {
        return format!(
            "first byte mismatch at {offset}: expected {expected:#04x}, actual {actual:#04x}"
        );
    }
    format!(
        "length mismatch: expected {} bytes, actual {} bytes",
        expected.len(),
        actual.len()
    )
}

#[test]
fn reviewed_reference_golden_decodes_and_reencodes_byte_exact() {
    assert!(PROVENANCE.contains(PIN_COMMIT));
    assert!(PROVENANCE.contains("Lean (version 4.32.0"));
    assert!(PROVENANCE.contains("deterministic: yes"));
    assert!(PROVENANCE.contains("update mode: none"));

    let expected = golden_bytes().expect("reviewed hexadecimal golden");
    let decoded =
        decode_ilean(&expected, IleanBudget::default()).expect("decode reviewed Reference golden");
    assert_eq!(decoded.version, 5);
    assert_eq!(decoded.module, "IleanProbe");
    assert!(decoded.direct_imports.is_empty());
    assert_eq!(decoded.decls.len(), 1);
    assert_eq!(decoded.references.len(), 2);
    assert!(decoded.references.contains_key(&IleanRefIdent::Const {
        module: "IleanProbe".to_string(),
        name: "localIdentity".to_string(),
    }));

    let actual = encode_ilean(&decoded, IleanBudget::default())
        .expect("re-encode reviewed Reference golden");
    assert_eq!(actual, expected, "{}", first_difference(&expected, &actual));
}

fn reference_lib() -> Option<PathBuf> {
    if let Ok(path) = std::env::var("FLN_REFERENCE_LIB") {
        let path = PathBuf::from(path);
        return path.is_dir().then_some(path);
    }
    let home = std::env::var("HOME").ok()?;
    let path = PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean");
    path.is_dir().then_some(path)
}

fn collect_ileans(root: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    let mut directories = vec![root.to_path_buf()];
    while let Some(directory) = directories.pop() {
        for entry in std::fs::read_dir(&directory).expect("readable Reference library directory") {
            let path = entry.expect("Reference library entry").path();
            if path.is_dir() {
                directories.push(path);
            } else if path
                .extension()
                .is_some_and(|extension| extension == "ilean")
            {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

#[test]
fn every_shipped_reference_ilean_reencodes_byte_identical() {
    let Some(root) = reference_lib() else {
        eprintln!("SKIP: pinned Reference stdlib not installed");
        return;
    };
    let files = collect_ileans(&root);
    assert!(
        files.len() > 2_400,
        "anti-vacuity: expected the pinned 2,433-file .ilean corpus, found {}",
        files.len()
    );
    let mut failures = Vec::new();
    for path in &files {
        let expected = std::fs::read(path).expect("readable Reference .ilean");
        let decoded = match decode_ilean(&expected, IleanBudget::default()) {
            Ok(decoded) => decoded,
            Err(error) => {
                failures.push(format!("{}: decode: {error}", path.display()));
                continue;
            }
        };
        let actual = match encode_ilean(&decoded, IleanBudget::default()) {
            Ok(actual) => actual,
            Err(error) => {
                failures.push(format!("{}: encode: {error}", path.display()));
                continue;
            }
        };
        if actual != expected {
            failures.push(format!(
                "{}: {}",
                path.display(),
                first_difference(&expected, &actual)
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {} pinned .ilean files diverged:\n{}",
        failures.len(),
        files.len(),
        failures.join("\n")
    );
}

#[test]
fn every_golden_truncation_refuses_and_byte_flips_never_break_totality() {
    let golden = golden_bytes().expect("reviewed hexadecimal golden");
    for end in 0..golden.len() {
        assert!(
            decode_ilean(&golden[..end], IleanBudget::default()).is_err(),
            "truncation at byte {end} was accepted"
        );
    }
    for offset in 0..golden.len() {
        let mut changed = golden.clone();
        changed[offset] ^= 0x80;
        if let Ok(decoded) = decode_ilean(&changed, IleanBudget::default()) {
            let encoded =
                encode_ilean(&decoded, IleanBudget::default()).expect("accepted value re-encodes");
            assert_eq!(
                decode_ilean(&encoded, IleanBudget::default()).expect("canonical re-decode"),
                decoded,
                "semantic round trip diverged after changing byte {offset}"
            );
        }
    }
}
