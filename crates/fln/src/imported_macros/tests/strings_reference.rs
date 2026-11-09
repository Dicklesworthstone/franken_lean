//! Actual imported user MacroM IR, selected under the hash-verified partition,
//! executes every string-literal row and compares complete syntax with the pin.
use super::*;
use fln_core::name::LeafView;
use std::{collections::BTreeMap, path::PathBuf, process::Command};

#[test]
fn live_pinned_string_literals_preserve_spelling_metadata_state_and_native_provenance() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from);
    let partition = std::env::var_os("FLN_REFERENCE_PARTITION").map(PathBuf::from);
    let (Some(reference), Some(partition)) = (reference, partition) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference and verified partition required for string literal macros"
        );
        eprintln!(
            "SKIP: string literal macros require FLN_REFERENCE_LEAN and FLN_REFERENCE_PARTITION"
        );
        return;
    };
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(
        String::from_utf8(version.stdout).unwrap().trim(),
        fln_olean::format::PIN_COMMIT
    );
    let partition =
        VerifiedPartition::from_pinned_tsv(&std::fs::read_to_string(partition).unwrap()).unwrap();
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir)
        .join(format!("string-macro-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let fixture = include_str!("../../../../fln-olean/fixtures/ir/StringMacroModule.lean");
    std::fs::write(dir.join("StringMacroModule.lean"), fixture).unwrap();
    let compiled = Command::new(&reference)
        .current_dir(&dir)
        .args(["-o", "StringMacroModule.olean", "StringMacroModule.lean"])
        .output()
        .unwrap();
    std::fs::write(dir.join("compile.stdout"), &compiled.stdout).unwrap();
    std::fs::write(dir.join("compile.stderr"), &compiled.stderr).unwrap();
    assert!(
        compiled.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&compiled.stdout),
        String::from_utf8_lossy(&compiled.stderr)
    );
    let module = crate::decode_ir_artifact(
        &std::fs::read(dir.join("StringMacroModule.ir")).unwrap(),
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
    let entries = [
        "genericLiteralMacro",
        "stringLiteralMacro",
        "quotedStringMacro",
        "inspectLiteralMacro",
        "inspectStringMacro",
        "typedStringMacro",
        "expandStringEcho",
    ];
    let macros: BTreeMap<_, _> = entries
        .into_iter()
        .map(|entry| {
            let compiled = compile(
                std::slice::from_ref(&module),
                &name(entry),
                &partition,
                &users,
                IrExecutionLimits::default(),
            )
            .unwrap_or_else(|error| panic!("{entry}: {error}; {dir:?}"));
            (entry, compiled)
        })
        .collect();
    let mut cases = Vec::new();
    for (value, spelling) in [
        ("", "\"\""),
        ("plain", "\"plain\""),
        ("'", "\"'\""),
        ("\n\r\t\\\"", "\"\\n\\x0d\\t\\\\\\\"\""),
        ("\0\u{1f}\u{7f}", "\"\\x00\\x1f\\x7f\""),
        ("λ🙂é\u{a0}", "\"λ🙂é\u{a0}\""),
    ] {
        for info in [
            SourceInfo::None,
            SourceInfo::Synthetic {
                pos: BytePos(0),
                end_pos: BytePos(4),
                canonical: false,
            },
            SourceInfo::Original {
                leading: span(0, 1),
                pos: BytePos(1),
                trailing: span(3, 4),
                end_pos: BytePos(3),
            },
        ] {
            let input = Syntax::Atom {
                info,
                val: value.into(),
            };
            cases.push((
                "genericLiteralMacro",
                input.clone(),
                lit("custom", value, info),
            ));
            cases.push((
                "stringLiteralMacro",
                input.clone(),
                lit("str", spelling, info),
            ));
            cases.push((
                "quotedStringMacro",
                input,
                lit("str", spelling, SourceInfo::None),
            ));
            let registered = Syntax::node(
                name("stringEcho"),
                vec![atom("stringEcho%"), lit("str", spelling, SourceInfo::None)],
            );
            cases.push((
                "expandStringEcho",
                registered,
                lit("str", spelling, SourceInfo::None),
            ));
        }
    }
    for (spelling, decoded) in [
        ("\"\"", Some("")),
        ("\"λ🙂\"", Some("λ🙂")),
        ("\"a\\n\\r\\t\\\\\\\"\\'b\"", Some("a\n\r\t\\\"'b")),
        ("\"\\x00\\x7F\\u03BB\\uD800\"", Some("\0\u{7f}λ\0")),
        ("\"a\\ b\"", Some("ab")),
        ("\"a\\\n\nb\"", Some("ab")),
        ("\"a\\\r\t b\"", Some("ab")),
        ("\"a\\\u{a0}b\"", None),
        ("\"abc\"trailing", Some("abc")),
        ("a\"", Some("")),
        ("λ\"", Some("A")),
        ("🙂x\"", Some("AAAx")),
        ("r", Some("")),
        ("r#", Some("")),
        ("rabc", Some("b")),
        ("r#abc", Some("")),
        ("r\"a\\n\"", Some("a\\n")),
        ("r##\"a\"#b\"##", Some("a\"#b")),
        ("r\"🙂", Some("🙂")),
        ("r#\"λ", Some("")),
        ("r#\"🙂", Some("🙂")),
        ("rλ🙂", Some("🙂")),
        ("", None),
        ("x", None),
        ("λ", None),
        ("\"unterminated", None),
        ("\"\\q\"", None),
        ("\"\\x0g\"", None),
        ("\"\\u0xyz\"", None),
    ] {
        let input = lit("str", spelling, SourceInfo::None);
        cases.push((
            "inspectStringMacro",
            input.clone(),
            decoded.map_or(Syntax::Missing, atom),
        ));
        cases.push(("typedStringMacro", input, atom(decoded.unwrap_or(""))));
        cases.push((
            "inspectLiteralMacro",
            lit("custom", spelling, SourceInfo::None),
            atom(spelling),
        ));
    }
    for input in [
        Syntax::Missing,
        atom("str"),
        Syntax::node(name("str"), vec![]),
        Syntax::node(name("str"), vec![atom("\"x\""), atom("\"y\"")]),
        Syntax::node(name("str"), vec![Syntax::Missing]),
        Syntax::node(name("str"), vec![lit("str", "\"x\"", SourceInfo::None)]),
        lit("Lean.str", "\"x\"", SourceInfo::None),
    ] {
        cases.push(("inspectStringMacro", input.clone(), Syntax::Missing));
        cases.push(("typedStringMacro", input.clone(), atom("")));
        cases.push(("inspectLiteralMacro", input, Syntax::Missing));
    }
    let state = MacroState {
        macro_scope: 23,
        trace_messages: vec![(name("trace"), "trace\0λ".into())],
        expanded_macro_declarations: vec![name("previous"), name("older.expansion")],
    };
    let mut rows = BTreeSet::new();
    let mut checks = Vec::new();
    for (entry, input, expected) in &cases {
        let report = macros[entry].execute(
            input,
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
                .all(|function| users.contains(&function.name)),
            "only this actual user module may execute interpreted IR: {entry}"
        );
        let Outcome::Complete(Ok(MacroResult::Expanded {
            syntax,
            state: next,
        })) = report.outcome
        else {
            panic!("{entry} on {input:?}: {:?}; {dir:?}", report.outcome);
        };
        assert_eq!(syntax, *expected, "{entry} on {input:?}");
        assert_eq!(next, state, "{entry} must preserve all three state fields");
        checks.push(format!(
            "checkString {entry} ({}) ({})",
            lean_syntax(input),
            lean_syntax(expected)
        ));
    }
    for helper in [
        "Lean.Syntax.mkLit",
        "Lean.Syntax.mkStrLit",
        "Lean.Syntax.isLit?",
        "Lean.Syntax.isStrLit?",
        "Lean.TSyntax.getString",
    ] {
        assert!(
            rows.contains(&format!("mirror:{helper}")),
            "actual user IR missed {helper}"
        );
    }
    let unsupported = macros["expandStringEcho"].execute(
        &Syntax::Missing,
        &source(),
        &context(),
        &state,
        MacroLimits::default(),
        None,
    );
    assert!(
        matches!(unsupported.outcome, Outcome::Complete(Ok(MacroResult::Unsupported { state: next })) if next == state)
    );
    check_stops(&macros["stringLiteralMacro"]);
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
    assert_eq!(observed.stdout, b"true\n", "{dir:?}");
    assert!(observed.stderr.is_empty());
    eprintln!(
        "native and pinned string literal macros: {} complete syntax/state cases",
        checks.len()
    );
}

fn atom(text: &str) -> Syntax {
    Syntax::Atom {
        info: SourceInfo::None,
        val: text.into(),
    }
}

fn lit(kind: &str, text: &str, info: SourceInfo) -> Syntax {
    Syntax::node(
        name(kind),
        vec![Syntax::Atom {
            info,
            val: text.into(),
        }],
    )
}

fn check_stops(compiled: &CompiledMacro) {
    let input = atom("\0");
    let state = MacroState::default();
    for syntax in [
        SyntaxLimits {
            max_nodes: 3,
            ..SyntaxLimits::default()
        },
        SyntaxLimits {
            max_bytes: 8,
            ..SyntaxLimits::default()
        },
    ] {
        let report = compiled.execute(
            &input,
            &source(),
            &context(),
            &state,
            MacroLimits {
                syntax,
                ..MacroLimits::default()
            },
            None,
        );
        assert!(
            matches!(report.outcome, Outcome::Inconclusive(_)),
            "{report:?}"
        );
        assert!(
            report.vm_usage.is_some(),
            "the result, not ingress, must exceed the allowance"
        );
    }
    for (vm, cancelled) in [
        (
            ExecutionLimits {
                max_steps: 0,
                ..ExecutionLimits::default()
            },
            false,
        ),
        (ExecutionLimits::default(), true),
    ] {
        let report = compiled.execute(
            &input,
            &source(),
            &context(),
            &state,
            MacroLimits {
                vm,
                ..MacroLimits::default()
            },
            Some(&|| cancelled),
        );
        assert!(
            matches!(report.outcome, Outcome::Inconclusive(_)),
            "{report:?}"
        );
    }
    let report = compiled.execute(
        &input,
        &source(),
        &context(),
        &state,
        MacroLimits::default(),
        None,
    );
    assert!(
        matches!(report.outcome, Outcome::Complete(Ok(MacroResult::Expanded { syntax, state: next }))
        if syntax == lit("str", "\"\\x00\"", SourceInfo::None) && next == state)
    );
}

fn lean_string(text: &str) -> String {
    let mut result = String::from("\"");
    for character in text.chars() {
        match character {
            '\\' => result.push_str("\\\\"),
            '"' => result.push_str("\\\""),
            character if character <= '\u{1f}' || character == '\u{7f}' => {
                use std::fmt::Write;
                write!(result, "\\x{:02x}", u32::from(character)).unwrap();
            }
            character => result.push(character),
        }
    }
    result.push('"');
    result
}

fn lean_name(value: &Name) -> String {
    match value.leaf_view() {
        LeafView::Anonymous => "Lean.Name.anonymous".into(),
        LeafView::Str(text) => format!(
            "Lean.Name.str ({}) {}",
            lean_name(&value.parent()),
            lean_string(text)
        ),
        LeafView::Num(number) => format!("Lean.Name.num ({}) {number}", lean_name(&value.parent())),
    }
}

fn lean_info(info: &SourceInfo) -> String {
    match info {
        SourceInfo::None => "Lean.SourceInfo.none".into(),
        SourceInfo::Synthetic {
            pos,
            end_pos,
            canonical,
        } => format!(
            "Lean.SourceInfo.synthetic ⟨{}⟩ ⟨{}⟩ {canonical}",
            pos.0, end_pos.0
        ),
        SourceInfo::Original {
            leading,
            pos,
            trailing,
            end_pos,
        } => format!(
            "Lean.SourceInfo.original ⟨\" α \", ⟨{}⟩, ⟨{}⟩⟩ ⟨{}⟩ ⟨\" α \", ⟨{}⟩, ⟨{}⟩⟩ ⟨{}⟩",
            leading.start().0,
            leading.end().0,
            pos.0,
            trailing.start().0,
            trailing.end().0,
            end_pos.0
        ),
    }
}

fn lean_syntax(value: &Syntax) -> String {
    match value {
        Syntax::Missing => "Lean.Syntax.missing".into(),
        Syntax::Atom { info, val } => format!(
            "Lean.Syntax.atom ({}) {}",
            lean_info(info),
            lean_string(val)
        ),
        Syntax::Node { info, kind, args } => format!(
            "Lean.Syntax.node ({}) ({}) #[{}]",
            lean_info(info),
            lean_name(kind),
            args.iter()
                .map(|child| format!("({})", lean_syntax(child)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Syntax::Ident { .. } => panic!("this literal fixture does not construct identifiers"),
    }
}

const ORACLE: &str = r#"
def sameSubstring (a b : Substring.Raw) : Bool :=
  a.str == b.str && a.startPos == b.startPos && a.stopPos == b.stopPos
def sameInfo : Lean.SourceInfo → Lean.SourceInfo → Bool
  | .none, .none => true
  | .synthetic p q c, .synthetic p' q' c' => p == p' && q == q' && c == c'
  | .original l p t q, .original l' p' t' q' =>
    sameSubstring l l' && p == p' && sameSubstring t t' && q == q'
  | _, _ => false
partial def sameSyntax : Lean.Syntax → Lean.Syntax → Bool
  | .missing, .missing => true
  | .atom i s, .atom i' s' => sameInfo i i' && s == s'
  | .node i k a, .node i' k' a' =>
    sameInfo i i' && k == k' && a.isEqv a' sameSyntax
  | _, _ => false
def stringScopes : Nat → Lean.MacroM Unit
  | 0 => pure ()
  | n + 1 => Lean.Macro.withFreshMacroScope (stringScopes n)
def checkString (f : Lean.Syntax → Lean.MacroM Lean.Syntax)
    (input expected : Lean.Syntax) : Bool :=
  let ctx : Lean.Macro.Context := ⟨default, `Main, 17, 0, 512, input⟩
  let state := match (do stringScopes 23; Lean.Macro.trace `trace "trace\x00λ") ctx default with
    | .ok _ state => state
    | .error _ state => state
  match f input ctx state with
  | .ok value next => sameSyntax value expected && next.macroScope == 23 &&
    next.traceMsgs == [(`trace, "trace\x00λ")]
  | _ => false
"#;
