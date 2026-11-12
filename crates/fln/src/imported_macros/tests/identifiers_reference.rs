use super::*;
use fln_core::name::{LeafView, hygiene::add_macro_scope};
use fln_syntax::tree::RawIdentifier;
use std::{path::PathBuf, process::Command};

#[test]
fn live_pinned_identifier_constructors_preserve_spelling_hygiene_positions_and_state() {
    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for identifier constructors"
        );
        eprintln!("SKIP: native identifier constructors require FLN_REFERENCE_LEAN");
        return;
    };
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(
        String::from_utf8(version.stdout).unwrap().trim(),
        fln_olean::format::PIN_COMMIT
    );
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir =
        std::env::temp_dir().join(format!("identifier-macro-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let fixture = include_str!("../../../../fln-olean/fixtures/ir/IdentifierMacroModule.lean");
    std::fs::write(dir.join("IdentifierMacroModule.lean"), fixture).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args([
            "-o",
            "IdentifierMacroModule.olean",
            "IdentifierMacroModule.lean",
        ])
        .output()
        .unwrap();
    assert!(
        generated.status.success(),
        "{}{}",
        String::from_utf8_lossy(&generated.stdout),
        String::from_utf8_lossy(&generated.stderr)
    );
    let module = crate::decode_ir_artifact(
        &std::fs::read(dir.join("IdentifierMacroModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .filter_map(|decl| match decl {
            IrDecl::Function { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    let macros = [
        ("identifierMacro", false, false, false),
        ("identifierFromMacro", false, true, false),
        ("canonicalIdentifierFromMacro", false, true, true),
        ("constantIdentifierMacro", true, false, false),
        ("constantIdentifierFromMacro", true, true, false),
        ("canonicalConstantIdentifierFromMacro", true, true, true),
    ]
    .map(|(entry, constant, from_ref, canonical)| {
        let compiled = compile(
            std::slice::from_ref(&module),
            &name(entry),
            &VerifiedPartition::user_fixture(),
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{entry}: {error}"));
        (entry, constant, from_ref, canonical, compiled)
    });
    let mut cases: Vec<(Name, String)> = vec![
        (Name::anonymous(), "[anonymous]".into()),
        (Name::str(Name::anonymous(), ""), "«»".into()),
        (name("Nat.succ"), "Nat.succ".into()),
        (Name::from_components(["A.B", "42"]), "«A.B».«42»".into()),
        (Name::from_components(["if", "then"]), "if.then".into()),
        (Name::from_components(["α₁", "é", "λ"]), "α₁.é.«λ»".into()),
        (
            Name::from_components(["漢", "🙂", "a\0b"]),
            "«漢».«🙂».«a\0b»".into(),
        ),
        (Name::from_components(["a»b", "«"]), "a»b.««»".into()),
        (Name::from_components(["?u", "a b"]), "?u.a b".into()),
        (Name::from_components(["#0", "a b"]), "#0.a b".into()),
        (Name::from_components(["_", "a b"]), "_.«a b»".into()),
        (
            Name::from_components(["a b", "_inaccessible"]),
            "a b._inaccessible".into(),
        ),
        (
            Name::num(Name::from_components(["a b", "x✝"]), 4),
            "a b.x✝.4".into(),
        ),
        (Name::from_components(["x✝", "a b"]), "«x✝».«a b»".into()),
        (
            Name::num(Name::str(Name::anonymous(), "42"), u64::MAX),
            "«42».18446744073709551615".into(),
        ),
        (Name::num(Name::anonymous(), 42), "42".into()),
    ];
    let scoped = add_macro_scope(&name("Other"), &Name::from_components(["a b", "λ"]), 7).unwrap();
    cases.push((scoped, "a b.λ._@.Other._hyg.7".into()));
    let state = MacroState {
        macro_scope: 23,
        trace_messages: vec![(name("trace"), "trace\0λ".into())],
        expanded_macro_declarations: vec![name("previous")],
    };
    let mut rows = BTreeSet::new();
    let mut checks = Vec::new();
    for (value, spelling) in cases {
        let protected = add_macro_scope(&name("_internal"), &value, 0).unwrap();
        for (info, positions, info_code) in [
            (SourceInfo::None, None, "Lean.SourceInfo.none"),
            (
                SourceInfo::Synthetic {
                    pos: BytePos(0),
                    end_pos: BytePos(4),
                    canonical: false,
                },
                Some((0, 4, false)),
                "Lean.SourceInfo.synthetic ⟨0⟩ ⟨4⟩ false",
            ),
            (
                SourceInfo::Original {
                    leading: span(0, 1),
                    pos: BytePos(1),
                    trailing: span(3, 4),
                    end_pos: BytePos(3),
                },
                Some((1, 3, true)),
                "Lean.SourceInfo.original ⟨\" α \", ⟨0⟩, ⟨1⟩⟩ ⟨1⟩ ⟨\" α \", ⟨3⟩, ⟨4⟩⟩ ⟨3⟩",
            ),
        ] {
            let input = Syntax::Ident {
                info,
                raw_val: span(1, 3).into(),
                val: value.clone(),
                preresolved: vec![Preresolved::Namespace {
                    ns: name("ignored"),
                }],
            };
            for (entry, constant, from_ref, canonical, compiled) in &macros {
                let expected_positions = if *from_ref {
                    positions.map(|(start, stop, original)| (start, stop, original && *canonical))
                } else {
                    None
                };
                let expected_info =
                    expected_positions.map_or(SourceInfo::None, |(start, stop, canonical)| {
                        SourceInfo::Synthetic {
                            pos: BytePos(start),
                            end_pos: BytePos(stop),
                            canonical,
                        }
                    });
                let (expected_name, raw, preresolved) = if *constant {
                    (
                        protected.clone(),
                        unescaped_name(&protected),
                        vec![Preresolved::Decl {
                            name: value.clone(),
                            fields: vec![],
                        }],
                    )
                } else {
                    (value.clone(), spelling.clone(), vec![])
                };
                let expected = Syntax::Ident {
                    info: expected_info,
                    raw_val: RawIdentifier::owned(raw.clone().into(), span(0, raw.len())).unwrap(),
                    val: expected_name.clone(),
                    preresolved,
                };
                let report = compiled.execute(
                    &input,
                    &source(),
                    &context(),
                    &state,
                    MacroLimits::default(),
                    None,
                );
                rows.extend(report.native_functions);
                assert!(
                    report
                        .reference_functions
                        .iter()
                        .all(|f| f.producer() == "reference"
                            && !f.name.to_display_string().starts_with("Lean.")),
                    "toolchain constructors must run natively"
                );
                let Outcome::Complete(Ok(MacroResult::Expanded {
                    syntax,
                    state: next,
                })) = report.outcome
                else {
                    panic!("{entry} on {value:?}: {:?}", report.outcome);
                };
                assert_eq!(syntax, expected, "{entry} on {value:?}");
                assert_eq!(next, state);
                let positions_code = expected_positions
                    .map_or("none".to_owned(), |(start, stop, canonical)| {
                        format!("some ({start}, {stop}, {canonical})")
                    });
                checks.push(format!(
                    "checkIdent {entry} ({info_code}) ({}) ({}) {} {} ({positions_code})",
                    lean_name(&value),
                    lean_name(&expected_name),
                    lean_string(&raw),
                    constant
                ));
            }
        }
    }
    for row in [
        "Lean.mkIdent",
        "Lean.mkIdentFrom",
        "Lean.mkCIdent",
        "Lean.mkCIdentFrom",
    ] {
        assert!(
            rows.contains(&format!("mirror:{row}")),
            "actual user macro missed {row}"
        );
    }
    let oracle = format!(
        "{fixture}\n{ORACLE}\n#eval ([{}] : List Bool).all id\n",
        checks.join(",\n    ")
    );
    std::fs::write(dir.join("Oracle.lean"), oracle).unwrap();
    let observed = Command::new(&reference)
        .current_dir(&dir)
        .arg("Oracle.lean")
        .output()
        .unwrap();
    std::fs::write(dir.join("oracle.stdout"), &observed.stdout).unwrap();
    std::fs::write(dir.join("oracle.stderr"), &observed.stderr).unwrap();
    assert!(
        observed.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&observed.stdout),
        String::from_utf8_lossy(&observed.stderr)
    );
    assert_eq!(observed.stdout, b"true\n");
    assert!(observed.stderr.is_empty());
    eprintln!(
        "native and pinned identifier constructors: {} exact identifiers",
        checks.len()
    );
}

fn lean_string(text: &str) -> String {
    format!(
        "\"{}\"",
        text.replace('\\', "\\\\")
            .replace('"', "\\\"")
            .replace('\0', "\\x00")
    )
}

// CIdent's reserved macro scope disables escaping. Retain every component,
// including an empty root: diagnostic display intentionally loses that detail.
fn unescaped_name(value: &Name) -> String {
    let mut parts = Vec::new();
    let mut cursor = value.clone();
    while !cursor.is_anonymous() {
        parts.push(match cursor.leaf_view() {
            LeafView::Str(text) => text.to_owned(),
            LeafView::Num(number) => number.to_string(),
            LeafView::Anonymous => unreachable!(),
        });
        cursor = cursor.parent();
    }
    parts.reverse();
    parts.join(".")
}

fn lean_name(value: &Name) -> String {
    let mut parts = Vec::new();
    let mut cursor = value.clone();
    while !cursor.is_anonymous() {
        parts.push(cursor.clone());
        cursor = cursor.parent();
    }
    let mut result = "Lean.Name.anonymous".to_owned();
    for part in parts.into_iter().rev() {
        result = match part.leaf_view() {
            LeafView::Str(text) => format!("Lean.Name.str ({result}) {}", lean_string(text)),
            LeafView::Num(number) => format!("Lean.Name.num ({result}) {number}"),
            LeafView::Anonymous => unreachable!(),
        };
    }
    result
}

const ORACLE: &str = r#"
def identifierScopes : Nat → Lean.MacroM Unit
  | 0 => pure ()
  | n + 1 => Lean.Macro.withFreshMacroScope (identifierScopes n)
def checkIdent (f : Lean.Syntax → Lean.MacroM Lean.Syntax) (info : Lean.SourceInfo)
    (inputName expectedName : Lean.Name) (text : String) (constant : Bool)
    (positions : Option (Nat × Nat × Bool)) : Bool :=
  let input := Lean.Syntax.ident info ⟨" α ", ⟨1⟩, ⟨3⟩⟩ inputName [.namespace `ignored]
  let ctx : Lean.Macro.Context := ⟨default, `Main, 17, 0, 512, input⟩
  let state := match (do identifierScopes 23; Lean.Macro.trace `trace "trace\x00λ") ctx default with
    | .ok _ state => state
    | .error _ state => state
  match f input ctx state with
  | .ok (.ident outInfo raw name pre) next =>
    let sameInfo := match positions, outInfo with
      | none, .none => true
      | some (start, stop, canonical), .synthetic pos endPos c =>
        pos.byteIdx == start && endPos.byteIdx == stop && c == canonical
      | _, _ => false
    let samePre := if constant then
      match pre with
      | [.decl declaration []] => declaration == inputName
      | _ => false
      else pre.isEmpty
    sameInfo && samePre && raw.str == text && raw.startPos.byteIdx == 0 &&
      raw.stopPos.byteIdx == text.utf8ByteSize && name == expectedName &&
      next.macroScope == 23 && next.traceMsgs == [(`trace, "trace\x00λ")]
  | _ => false
"#;
