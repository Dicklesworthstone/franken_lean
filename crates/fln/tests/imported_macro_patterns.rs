//! Actual user MacroM IR exercises quotation-pattern services under the pinned
//! partition. The oracle compares complete syntax, source metadata and state.
#![forbid(unsafe_code)]

use fln::imported_ir::{IrExecutionLimits, VerifiedPartition};
use fln::imported_macros::{MacroContext, MacroLimits, MacroResult, MacroState, compile};
use fln_core::name::{LeafView, Name};
use fln_core::outcome::Outcome;
use fln_olean::ir::IrDecl;
use fln_syntax::source::{BytePos, ByteSpan, SourceInfo, SourceText};
use fln_syntax::tree::{Preresolved, RawIdentifier, Syntax};
use fln_vm::interpreter::ExecutionLimits;
use std::{collections::BTreeSet, path::PathBuf, process::Command};

#[test]
fn live_pinned_quotation_patterns_preserve_hygiene_shapes_metadata_and_state() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from);
    let partition = std::env::var_os("FLN_REFERENCE_PARTITION").map(PathBuf::from);
    let (Some(reference), Some(partition)) = (reference, partition) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference and verified partition required for quotation patterns"
        );
        eprintln!(
            "SKIP: quotation patterns require FLN_REFERENCE_LEAN and FLN_REFERENCE_PARTITION"
        );
        return;
    };
    let version = Command::new(&reference)
        .args(["-j1", "--githash"])
        .output()
        .unwrap();
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
        .join(format!("pattern-macro-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let fixture = include_str!("../../fln-olean/fixtures/ir/PatternMacroModule.lean");
    std::fs::write(dir.join("PatternMacroModule.lean"), fixture).unwrap();
    let emitted = Command::new(&reference)
        .current_dir(&dir)
        .args([
            "-j1",
            "-o",
            "PatternMacroModule.olean",
            "PatternMacroModule.lean",
        ])
        .output()
        .unwrap();
    std::fs::write(dir.join("compile.stdout"), &emitted.stdout).unwrap();
    std::fs::write(dir.join("compile.stderr"), &emitted.stderr).unwrap();
    assert!(
        emitted.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&emitted.stdout),
        String::from_utf8_lossy(&emitted.stderr)
    );
    let module = fln::decode_ir_artifact(
        &std::fs::read(dir.join("PatternMacroModule.ir")).unwrap(),
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
    let compiled = compile(
        std::slice::from_ref(&module),
        &name("patternServicesMacro"),
        &partition,
        &users,
        IrExecutionLimits::default(),
    )
    .unwrap_or_else(|error| panic!("patternServicesMacro: {error}; {dir:?}"));
    let separated = compile(
        std::slice::from_ref(&module),
        &name("separatedServicesMacro"),
        &partition,
        &users,
        IrExecutionLimits::default(),
    )
    .unwrap_or_else(|error| panic!("separatedServicesMacro: {error}; {dir:?}"));
    let state = MacroState {
        macro_scope: 23,
        trace_messages: vec![(name("trace"), "trace\0λ".into())],
        expanded_macro_declarations: vec![name("previous"), name("older.expansion")],
    };
    let mut rows = BTreeSet::new();
    let mut checks = Vec::new();
    let cases = cases();
    for (input, expected) in &cases {
        let report = compiled.execute(
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
            "toolchain pattern services must execute natively"
        );
        let Outcome::Complete(Ok(MacroResult::Expanded {
            syntax,
            state: next,
        })) = report.outcome
        else {
            panic!(
                "patternServicesMacro on {input:?}: {:?}; {dir:?}",
                report.outcome
            );
        };
        assert_eq!(syntax, *expected, "input: {input:?}");
        assert_eq!(
            next, state,
            "all MacroM state fields must survive pattern inspection"
        );
        checks.push(format!(
            "checkPattern ({}) ({})",
            lean_syntax(input),
            lean_syntax(expected)
        ));
    }
    for helper in [
        "Lean.Name.hasMacroScopes",
        "Lean.Name.eraseMacroScopes",
        "Lean.Syntax.isNodeOf",
        "Lean.Syntax.matchesNull",
        "Lean.Syntax.matchesIdent",
        "Lean.Syntax.matchesLit",
        "Lean.Syntax.getOptional?",
    ] {
        assert!(
            rows.contains(&format!("mirror:{helper}")),
            "actual user MacroM IR missed {helper}"
        );
    }
    let separated_cases = separated_cases();
    for (input, expected) in &separated_cases {
        let report = separated.execute(
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
            "repetition services must execute natively"
        );
        let Outcome::Complete(Ok(MacroResult::Expanded {
            syntax,
            state: next,
        })) = report.outcome
        else {
            panic!(
                "separatedServicesMacro on {input:?}: {:?}; {dir:?}",
                report.outcome
            );
        };
        assert_eq!(syntax, *expected, "input: {input:?}");
        assert_eq!(next, state);
        checks.push(format!(
            "checkSeparated ({}) ({})",
            lean_syntax(input),
            lean_syntax(expected)
        ));
    }
    for helper in [
        "Lean.mkSepArray",
        "Lean.Syntax.mkSep",
        "Lean.Syntax.getSepArgs",
        "Lean.Syntax.SepArray.getElems._redArg",
        "Lean.Syntax.TSepArray.getElems._redArg",
    ] {
        assert!(
            rows.contains(&format!("mirror:{helper}")),
            "actual user MacroM IR missed {helper}"
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
        for (compiled, input) in [
            (&compiled, &cases[0].0),
            (&separated, &separated_cases[0].0),
        ] {
            let report = compiled.execute(
                input,
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
    }
    let resumed = compiled.execute(
        &cases[0].0,
        &source(),
        &context(),
        &state,
        MacroLimits::default(),
        None,
    );
    assert!(
        matches!(resumed.outcome, Outcome::Complete(Ok(MacroResult::Expanded { syntax, state: next })) if syntax == cases[0].1 && next == state)
    );
    let resumed = separated.execute(
        &separated_cases[0].0,
        &source(),
        &context(),
        &state,
        MacroLimits::default(),
        None,
    );
    assert!(
        matches!(resumed.outcome, Outcome::Complete(Ok(MacroResult::Expanded { syntax, state: next })) if syntax == separated_cases[0].1 && next == state)
    );
    std::fs::write(
        dir.join("Oracle.lean"),
        format!(
            "{fixture}\n{ORACLE}\n#eval ([{}] : List Bool).all id\n",
            checks.join(",\n    ")
        ),
    )
    .unwrap();
    let observed = Command::new(&reference)
        .current_dir(&dir)
        .args(["-j1", "Oracle.lean"])
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
        "native and pinned quotation patterns/repetitions: {} complete syntax/state cases",
        checks.len()
    );
}

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn span(start: usize, end: usize) -> ByteSpan {
    ByteSpan::new(BytePos(start), BytePos(end)).unwrap()
}

fn source() -> SourceText {
    SourceText::from_utf8(" α ".as_bytes()).unwrap()
}

fn context() -> MacroContext {
    MacroContext {
        quotation_context: name("Main"),
        current_macro_scope: 17,
        current_recursion_depth: 0,
        max_recursion_depth: 512,
    }
}

fn leaf() -> Syntax {
    Syntax::Ident {
        info: SourceInfo::Original {
            leading: span(0, 1),
            pos: BytePos(1),
            trailing: span(3, 4),
            end_pos: BytePos(3),
        },
        raw_val: span(1, 3).into(),
        val: Name::num(name("Main._hyg"), 17),
        preresolved: vec![
            Preresolved::Namespace { ns: name("N") },
            Preresolved::Decl {
                name: name("N.x"),
                fields: vec!["field".into()],
            },
        ],
    }
}

fn atom(text: &str) -> Syntax {
    Syntax::atom(SourceInfo::None, text)
}

fn ident(value: Name) -> Syntax {
    Syntax::Ident {
        info: SourceInfo::None,
        raw_val: RawIdentifier::owned("".into(), span(0, 0)).unwrap(),
        val: value,
        preresolved: vec![],
    }
}

fn separated_cases() -> Vec<(Syntax, Syntax)> {
    let marked_separator = Syntax::Atom {
        info: SourceInfo::Synthetic {
            pos: BytePos(1),
            end_pos: BytePos(3),
            canonical: true,
        },
        val: "λ\0".into(),
    };
    let cases = [
        (vec![], Syntax::Missing, Syntax::Missing, vec![]),
        (vec![leaf()], atom(","), atom("null"), vec![]),
        (
            vec![leaf(), atom("b")],
            marked_separator.clone(),
            Syntax::node(name("null"), vec![leaf(), atom(","), atom("b")]),
            vec![leaf(), atom("b")],
        ),
        (
            vec![Syntax::Missing, atom("b"), leaf()],
            leaf(),
            Syntax::node(
                name("arbitrary.node"),
                vec![leaf(), atom(";"), atom("b"), marked_separator.clone()],
            ),
            vec![leaf(), atom("b")],
        ),
        (vec![atom("x")], Syntax::Missing, leaf(), vec![]),
        (
            vec![],
            marked_separator.clone(),
            Syntax::node(name("arbitrary"), vec![Syntax::Missing]),
            vec![Syntax::Missing],
        ),
        (
            vec![leaf(), Syntax::Missing],
            Syntax::node(name("separator"), vec![marked_separator]),
            Syntax::node(name("arbitrary"), vec![leaf(), Syntax::Missing]),
            vec![leaf()],
        ),
    ];
    cases
        .into_iter()
        .map(|(values, separator, candidate, extracted)| {
            let mut separated = Vec::new();
            for value in &values {
                if !separated.is_empty() {
                    separated.push(separator.clone());
                }
                separated.push(value.clone());
            }
            let built = Syntax::node(name("null"), separated);
            let extracted = Syntax::node(name("null"), extracted);
            (
                Syntax::node(
                    name("separatedInput"),
                    vec![Syntax::node(name("values"), values), separator, candidate],
                ),
                Syntax::node(
                    name("separatedResult"),
                    vec![
                        built.clone(),
                        built,
                        extracted.clone(),
                        extracted.clone(),
                        extracted,
                    ],
                ),
            )
        })
        .collect()
}

struct Shape {
    kind: &'static str,
    size: &'static str,
    literal: Syntax,
    optional: Syntax,
    candidate: Syntax,
    matches: [bool; 3],
    extracted: Syntax,
}

fn cases() -> Vec<(Syntax, Syntax)> {
    let raw = "λ\0";
    let lit = |kind: &str, children| Syntax::node(name(kind), children);
    let optional = || lit("null", vec![leaf()]);
    let shapes = [
        Shape {
            kind: "str",
            size: "1",
            literal: lit("str", vec![atom(raw)]),
            optional: optional(),
            candidate: lit("str", vec![Syntax::Missing]),
            matches: [true, true, true],
            extracted: leaf(),
        },
        Shape {
            kind: "str",
            size: "0",
            literal: lit("str", vec![atom(raw), atom("extra")]),
            optional: atom("null"),
            candidate: atom("str"),
            matches: [true, true, true],
            extracted: Syntax::Missing,
        },
        Shape {
            kind: "str",
            size: "2",
            literal: lit("str", vec![]),
            optional: lit("null", vec![atom("a"), atom("b")]),
            candidate: lit("str", vec![atom("a")]),
            matches: [false, true, false],
            extracted: Syntax::Missing,
        },
        Shape {
            kind: "ident",
            size: "0",
            literal: lit("ident", vec![atom(raw)]),
            optional: Syntax::Missing,
            candidate: leaf(),
            matches: [true, false, true],
            extracted: Syntax::Missing,
        },
        Shape {
            kind: "missing",
            size: "0",
            literal: atom(raw),
            optional: lit("null", vec![]),
            candidate: Syntax::Missing,
            matches: [false, true, true],
            extracted: Syntax::Missing,
        },
        Shape {
            kind: "str",
            size: "18446744073709551616",
            literal: lit("str", vec![atom(raw)]),
            optional: optional(),
            candidate: lit("str", vec![leaf()]),
            matches: [true, false, false],
            extracted: leaf(),
        },
        Shape {
            kind: "num",
            size: "1",
            literal: lit("str", vec![atom(raw)]),
            optional: lit("other", vec![leaf()]),
            candidate: lit("num", vec![]),
            matches: [false, false, false],
            extracted: Syntax::Missing,
        },
        Shape {
            kind: "null",
            size: "0",
            literal: lit("null", vec![Syntax::Missing]),
            optional: atom("null"),
            candidate: lit("null", vec![]),
            matches: [false, true, true],
            extracted: Syntax::Missing,
        },
        Shape {
            kind: "str",
            size: "1",
            literal: lit("str", vec![atom("other")]),
            optional: lit("null", vec![Syntax::Missing]),
            candidate: atom("str"),
            matches: [false, true, false],
            extracted: Syntax::Missing,
        },
    ];
    let plain = name("A.λ");
    let scoped = Name::num(name("A.λ._@.First._hyg"), 7);
    let other_scope = Name::num(name("A.λ._@.Second._hyg"), 9);
    let id_cases = [
        (plain.clone(), plain.clone(), false, plain.clone(), true),
        (scoped.clone(), other_scope, true, plain.clone(), true),
        (plain.clone(), scoped.clone(), false, plain.clone(), true),
        (
            plain.clone(),
            Name::str(Name::anonymous(), "A.λ"),
            false,
            plain.clone(),
            false,
        ),
        (
            Name::str(scoped.clone(), "field"),
            plain,
            false,
            Name::str(scoped, "field"),
            false,
        ),
        (
            Name::num(name("A._hyg"), 3),
            Name::anonymous(),
            true,
            Name::anonymous(),
            true,
        ),
        (
            Name::num(name("A._@.B._@.M._hyg"), 4),
            name("A._@.B"),
            true,
            name("A._@.B"),
            true,
        ),
    ];
    let mut result = Vec::new();
    for (id, target, has_scopes, erased, ident_match) in id_cases {
        for shape in &shapes {
            result.push((
                lit(
                    "patternInput",
                    vec![
                        ident(id.clone()),
                        ident(target.clone()),
                        ident(name(shape.kind)),
                        lit("num", vec![atom(shape.size)]),
                        shape.literal.clone(),
                        atom(raw),
                        shape.optional.clone(),
                        shape.candidate.clone(),
                    ],
                ),
                lit(
                    "patternResult",
                    vec![
                        atom(if has_scopes { "true" } else { "false" }),
                        ident(erased.clone()),
                        atom(if ident_match { "true" } else { "false" }),
                        atom(if shape.matches[0] { "true" } else { "false" }),
                        atom(if shape.matches[1] { "true" } else { "false" }),
                        atom(if shape.matches[2] { "true" } else { "false" }),
                        shape.extracted.clone(),
                    ],
                ),
            ));
        }
    }
    result
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
                .map(|value| format!("({})", lean_syntax(value)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Syntax::Ident {
            info,
            raw_val,
            val,
            preresolved,
        } => format!(
            "Lean.Syntax.ident ({}) ⟨{}, ⟨{}⟩, ⟨{}⟩⟩ ({}) [{}]",
            lean_info(info),
            lean_string(raw_val.backing(&source())),
            raw_val.span().start().0,
            raw_val.span().end().0,
            lean_name(val),
            preresolved
                .iter()
                .map(|entry| match entry {
                    Preresolved::Namespace { ns } => format!(".namespace ({})", lean_name(ns)),
                    Preresolved::Decl { name, fields } => format!(
                        ".decl ({}) [{}]",
                        lean_name(name),
                        fields
                            .iter()
                            .map(|field| lean_string(field))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                })
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

const ORACLE: &str = r#"
def patternScopes : Nat → Lean.MacroM Unit
  | 0 => pure ()
  | n + 1 => Lean.Macro.withFreshMacroScope (patternScopes n)
def checkPattern (input expected : Lean.Syntax) : Bool :=
  let context : Lean.Macro.Context := ⟨default, `Main, 17, 0, 512, input⟩
  let state := match (do patternScopes 23; Lean.Macro.trace `trace "trace\x00λ") context default with
    | .ok _ state => state
    | .error _ state => state
  match patternServicesMacro input context state with
  | .ok result next =>
    result.eqWithInfo expected && next.macroScope == 23 && next.traceMsgs == [(`trace, "trace\x00λ")]
  | _ => false
def checkSeparated (input expected : Lean.Syntax) : Bool :=
  let context : Lean.Macro.Context := ⟨default, `Main, 17, 0, 512, input⟩
  let state := match (do patternScopes 23; Lean.Macro.trace `trace "trace\x00λ") context default with
    | .ok _ state => state
    | .error _ state => state
  match separatedServicesMacro input context state with
  | .ok result next =>
    result.eqWithInfo expected && next.macroScope == 23 && next.traceMsgs == [(`trace, "trace\x00λ")]
  | _ => false
"#;
