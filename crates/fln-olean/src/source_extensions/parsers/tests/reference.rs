//! The complete final journal emitted by the exact pinned Reference, including
//! category-generated syntax and scoped tokens whose kinds remain global.
use super::*;
use crate::region::{OleanView, WalkBudget};
use std::path::PathBuf;
use std::process::Command;

#[test]
fn live_parser_journal_preserves_category_leading_trailing_and_scoped_entries() {
    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for parser journal decoding"
        );
        eprintln!("SKIP: parser journal requires FLN_REFERENCE_LEAN");
        return;
    };
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(
        String::from_utf8(version.stdout).unwrap().trim(),
        crate::format::PIN_COMMIT
    );
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!("parser-journal-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let source = r#"module
prelude
public import Init
public section

declare_syntax_cat importedData (behavior := both)
syntax (name := importedAtom) (priority := 1200) "datum%" num : importedData
syntax:65 (name := importedJoin) (priority := 1100) importedData:65 " +% " importedData:66 : importedData
syntax (name := importedUse) "useDatum%" importedData : term

namespace Enabled
scoped syntax (name := importedScoped) (priority := 1300) "scopedDatum%" "endDatum%" : importedData
end Enabled
"#;
    std::fs::write(dir.join("NativeParserJournal.lean"), source).unwrap();
    let result = Command::new(&reference)
        .current_dir(&dir)
        .args([
            "-o",
            "NativeParserJournal.olean",
            "NativeParserJournal.lean",
        ])
        .output()
        .unwrap();
    std::fs::write(dir.join("compile.stdout"), &result.stdout).unwrap();
    std::fs::write(dir.join("compile.stderr"), &result.stderr).unwrap();
    assert!(
        result.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
    let public = std::fs::read(dir.join("NativeParserJournal.olean")).unwrap();
    let companions = (
        std::fs::read(dir.join("NativeParserJournal.olean.server")),
        std::fs::read(dir.join("NativeParserJournal.olean.private")),
    );
    let (Ok(server), Ok(private)) = companions else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "parser journal requires both pinned module companions: {dir:?}"
        );
        eprintln!("SKIP: complete parser journal companions absent: {dir:?}");
        return;
    };
    let blocks = OleanView::parse_with_dependencies(&private, &[&public, &server])
        .unwrap()
        .extension_payloads(WalkBudget::default(), 32 << 20)
        .unwrap();
    let raw = blocks
        .iter()
        .find(|block| block.name == extension_name())
        .expect("Reference emitted its parser journal");
    let decoded = decode(&blocks, DecodeLimits::default()).unwrap();
    assert_eq!(decoded.entries.len(), raw.entries.len());
    assert!(decoded.entries.iter().any(|row| matches!(
        row,
        ParserEntry {
            scope: None,
            kind: ParserEntryKind::Category { category, declaration, behavior: LeadingIdentBehavior::Both }
        } if *category == name("importedData") && *declaration == name("Lean.Parser.Category.importedData")
    )));
    let selected = [
        name("importedAtom"),
        name("importedJoin"),
        name("Enabled.importedScoped"),
    ];
    let registrations: Vec<_> = decoded
        .entries
        .iter()
        .filter_map(|row| {
            let ParserEntryKind::Parser {
                category,
                declaration,
                priority,
            } = &row.kind
            else {
                return None;
            };
            selected.contains(declaration).then(|| {
                (
                    category.clone(),
                    declaration.clone(),
                    *priority,
                    row.scope.clone(),
                )
            })
        })
        .collect();
    assert_eq!(
        registrations,
        [
            (name("importedData"), selected[0].clone(), 1200, None),
            (name("importedData"), selected[1].clone(), 1100, None),
            (
                name("importedData"),
                selected[2].clone(),
                1300,
                Some(name("Enabled"))
            ),
        ]
    );
    let scoped_token = decoded
        .entries
        .iter()
        .position(|row| {
            matches!(
                row,
                ParserEntry { scope: Some(scope), kind: ParserEntryKind::Token(token) }
            if *scope == name("Enabled") && token == "endDatum%"
            )
        })
        .unwrap();
    let scoped_kind = decoded
        .entries
        .iter()
        .position(|row| {
            matches!(
                row,
                ParserEntry { scope: None, kind: ParserEntryKind::Kind(kind) }
                    if *kind == selected[2]
            )
        })
        .unwrap();
    let scoped_parser = decoded.entries.iter().position(|row| matches!(
        row,
        ParserEntry { scope: Some(scope), kind: ParserEntryKind::Parser { declaration, .. } }
            if *scope == name("Enabled") && *declaration == selected[2]
    )).unwrap();
    assert!(scoped_token < scoped_kind && scoped_kind < scoped_parser);
    assert!(
        !decoded.entries.iter().any(|row| matches!(
            &row.kind, ParserEntryKind::Token(token) if token == "scopedDatum%"
        )),
        "Both identifier behavior leaves the first atom nonreserved"
    );

    // The complete captured journal is atomic even if a malformed row follows
    // all of the real registrations.
    let mut corrupt = raw.clone();
    corrupt.entries.push(compact(&Obj::mk_nat(0), 0).unwrap());
    assert!(matches!(
        decode(&[corrupt], DecodeLimits::default()),
        Err(DecodeError::Shape { .. })
    ));
}

/// No oracle process is needed: these are the actual pinned release artifacts.
/// Source assertions come from vendored `src/Init/Conv.lean`, especially its
/// category declaration, scoped withAnnotateState, and ordered skip/cbv/lhs/rhs.
#[test]
fn installed_reference_conv_journal_decodes_every_row_without_execution() {
    let Some(lib) = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference library required for parser artifact decoding"
        );
        eprintln!("SKIP: installed parser journal requires FLN_REFERENCE_LIB");
        return;
    };
    let path = lib.join("Init/Conv.olean");
    let public = std::fs::read(&path).expect("pinned Init.Conv public artifact");
    let server = std::fs::read(path.with_extension("olean.server"))
        .expect("pinned Init.Conv server artifact");
    let private = std::fs::read(path.with_extension("olean.private"))
        .expect("pinned Init.Conv private artifact");
    let view = OleanView::parse_with_dependencies(&private, &[&public, &server]).unwrap();
    assert_eq!(view.header.githash, crate::format::PIN_COMMIT);
    let blocks = view
        .extension_payloads(WalkBudget::default(), 32 << 20)
        .unwrap();
    let raw = blocks
        .iter()
        .find(|block| block.name == extension_name())
        .expect("Init.Conv contains a parser journal");
    let decoded = decode(&blocks, DecodeLimits::default()).unwrap();
    assert_eq!(decoded.entries.len(), raw.entries.len());
    let mut variants = [0usize; 4];
    for row in &decoded.entries {
        variants[match row.kind {
            ParserEntryKind::Token(_) => 0,
            ParserEntryKind::Kind(_) => 1,
            ParserEntryKind::Category { .. } => 2,
            ParserEntryKind::Parser { .. } => 3,
        }] += 1;
    }
    assert!(variants.iter().all(|count| *count > 0), "{variants:?}");
    let category_at = decoded.entries.iter().position(|row| matches!(
        row,
        ParserEntry {
            scope: None,
            kind: ParserEntryKind::Category { category, declaration, behavior: LeadingIdentBehavior::Both }
        } if *category == name("conv") && *declaration == name("Lean.Parser.Category.conv")
    )).unwrap();
    let scoped_name = name("Lean.Parser.Tactic.Conv.withAnnotateState");
    let scoped_kind_at = decoded.entries.iter().position(|row| matches!(
        row,
        ParserEntry { scope: None, kind: ParserEntryKind::Kind(kind) } if *kind == scoped_name
    )).unwrap();
    let scoped_parser_at = decoded.entries.iter().position(|row| matches!(
        row,
        ParserEntry {
            scope: Some(scope),
            kind: ParserEntryKind::Parser { category, declaration, .. }
        } if *scope == name("Lean.Parser.Tactic.Conv") && *category == name("conv") && *declaration == scoped_name
    )).unwrap();
    assert!(category_at < scoped_kind_at && scoped_kind_at < scoped_parser_at);
    let expected =
        ["skip", "cbv", "lhs", "rhs"].map(|leaf| Name::str(name("Lean.Parser.Tactic.Conv"), leaf));
    let ordered: Vec<_> = decoded
        .entries
        .iter()
        .filter_map(|row| match &row.kind {
            ParserEntryKind::Parser {
                category,
                declaration,
                ..
            } if expected.contains(declaration) => {
                assert_eq!(*category, name("conv"));
                assert!(row.scope.is_none());
                Some(declaration.clone())
            }
            _ => None,
        })
        .collect();
    assert_eq!(ordered, expected);
    eprintln!(
        "Init.Conv complete parser journal: {} rows, token/kind/category/parser counts {variants:?}",
        decoded.entries.len()
    );
}
