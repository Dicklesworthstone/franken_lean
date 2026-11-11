//! Sequence construction through actual user MacroM IR. Toolchain sequence
//! implementations stay native, while the live pinned oracle checks every
//! source field, raw identifier, hygiene identity and successor-state field.
use super::*;
use fln_syntax::tree::RawIdentifier;
use std::{collections::BTreeMap, path::PathBuf, process::Command};

#[test]
fn live_pinned_sequence_builders_preserve_syntax_state_and_generated_terms() {
    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for sequence builders"
        );
        eprintln!("SKIP: native sequence builders require FLN_REFERENCE_LEAN");
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
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir)
        .join(format!("sequence-macro-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let fixture = include_str!("../../../../fln-olean/fixtures/ir/SequenceMacroModule.lean");
    std::fs::write(dir.join("SequenceMacroModule.lean"), fixture).unwrap();
    let emitted = Command::new(&reference)
        .current_dir(&dir)
        .args([
            "-j1",
            "-o",
            "SequenceMacroModule.olean",
            "SequenceMacroModule.lean",
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
    let module = crate::decode_ir_artifact(
        &std::fs::read(dir.join("SequenceMacroModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    // This fixture contains only its own emitted declarations. It supplies no
    // imported/toolchain IR that a synthetic partition could relabel as user code.
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .filter_map(|declaration| match declaration {
            IrDecl::Function { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    let macros: BTreeMap<_, _> = [
        "untypedSequenceMacro",
        "emptySeparatorMacro",
        "typedSequenceMacro",
        "appendSequenceMacro",
        "appendEmptySeparatorMacro",
        "expandFirstSequence",
    ]
    .into_iter()
    .map(|entry| {
        let compiled = compile(
            std::slice::from_ref(&module),
            &name(entry),
            &VerifiedPartition::user_fixture(),
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{entry}: {error}; {dir:?}"));
        (entry, compiled)
    })
    .collect();
    let state = MacroState {
        macro_scope: 23,
        trace_messages: vec![(name("trace"), "trace\0λ".into())],
        expanded_macro_declarations: vec![name("previous"), name("older.expansion")],
    };
    let mut cases = Vec::new();
    let children = [
        leaf(),
        Syntax::Ident {
            info: SourceInfo::Synthetic {
                pos: BytePos(1),
                end_pos: BytePos(3),
                canonical: true,
            },
            raw_val: RawIdentifier::owned("xλy".into(), span(1, 3)).unwrap(),
            val: fln_core::name::hygiene::add_macro_scope(
                &name("Imported"),
                &name("scoped.local"),
                42,
            )
            .unwrap(),
            preresolved: vec![Preresolved::Decl {
                name: name("Other.value"),
                fields: vec!["field".into(), "λ".into()],
            }],
        },
        Syntax::Atom {
            info: SourceInfo::Synthetic {
                pos: BytePos(0),
                end_pos: BytePos(4),
                canonical: false,
            },
            val: "λ,\0".into(),
        },
        Syntax::Missing,
        Syntax::node(name("nested"), vec![leaf(), atom("different separator")]),
    ];
    for count in 0..=children.len() {
        let input = Syntax::Node {
            info: leaf().info(),
            kind: name("input"),
            args: children[..count].to_vec(),
        };
        for (entry, separator, append) in [
            ("untypedSequenceMacro", ",", false),
            ("emptySeparatorMacro", "", false),
            ("typedSequenceMacro", ",", false),
            ("appendSequenceMacro", ",", true),
            ("appendEmptySeparatorMacro", "", true),
        ] {
            let expected = if append {
                appended(&children[..count], separator)
            } else {
                separated(&children[..count], separator)
            };
            cases.push((entry, input.clone(), expected));
        }
    }
    for input in [Syntax::Missing, atom("not a node"), leaf()] {
        cases.push(("untypedSequenceMacro", input.clone(), null(vec![])));
        cases.push(("appendSequenceMacro", input, null(vec![atom("tail")])));
    }
    for terms in [
        vec![],
        vec![number("7")],
        vec![number("7"), number("11")],
        vec![number("7"), number("11"), number("13")],
        vec![leaf()],
    ] {
        let expected = terms.first().cloned().unwrap_or_else(|| number("42"));
        cases.push(("expandFirstSequence", first_sequence(&terms), expected));
    }
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
                .all(|function| function.producer() == "reference"
                    && users.contains(&function.name)
                    && !function.name.to_display_string().starts_with("Lean.")),
            "only this user module may run interpreted IR: {entry}"
        );
        let Outcome::Complete(Ok(MacroResult::Expanded {
            syntax,
            state: next,
        })) = report.outcome
        else {
            panic!("{entry} on {input:?}: {:?}; {dir:?}", report.outcome);
        };
        assert_eq!(syntax, *expected, "{entry} on {input:?}");
        assert_eq!(next, state, "all three state fields survive {entry}");
        checks.push(format!(
            "checkSequence {entry} ({}) ({})",
            lean_syntax(input),
            lean_syntax(expected)
        ));
    }
    for row in [
        "mirror:Lean.Syntax.SepArray.ofElems",
        "mirror:Lean.Syntax.TSepArray.push._redArg",
    ] {
        assert!(rows.contains(row), "actual user IR missed {row}");
    }
    for input in [Syntax::Missing, Syntax::node(name("otherSequence"), vec![])] {
        let report = macros["expandFirstSequence"].execute(
            &input,
            &source(),
            &context(),
            &state,
            MacroLimits::default(),
            None,
        );
        assert!(
            matches!(report.outcome, Outcome::Complete(Ok(MacroResult::Unsupported { state: next })) if next == state)
        );
        checks.push(format!(
            "checkSequenceUnsupported expandFirstSequence ({})",
            lean_syntax(&input)
        ));
    }
    check_stops(&macros);
    check_generated_source(&macros["expandFirstSequence"]);
    // Only the oracle imports the private State constructor and projection
    // needed to compare all three fields. The user IR fixture stays unchanged.
    let oracle_fixture = fixture.replacen(
        "public import Init\n",
        "public import Init\nimport all Init.Prelude\n",
        1,
    );
    let oracle = format!(
        "{oracle_fixture}\n{ORACLE}\n#eval ([{}] : List Bool).all id\n",
        checks.join(",\n    ")
    );
    std::fs::write(dir.join("Oracle.lean"), oracle).unwrap();
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
        "native and pinned sequence builders: {} complete syntax/state cases plus generated-source admission",
        checks.len()
    );
}

fn atom(text: &str) -> Syntax {
    Syntax::Atom {
        info: SourceInfo::None,
        val: text.into(),
    }
}
fn null(args: Vec<Syntax>) -> Syntax {
    Syntax::node(name("null"), args)
}
fn number(text: &str) -> Syntax {
    Syntax::node(name("num"), vec![atom(text)])
}

fn separated(elements: &[Syntax], separator: &str) -> Syntax {
    let mut parts = Vec::new();
    for (index, element) in elements.iter().enumerate() {
        if index != 0 {
            parts.push(if separator.is_empty() {
                null(vec![])
            } else {
                atom(separator)
            });
        }
        parts.push(element.clone());
    }
    null(parts)
}

fn appended(parts: &[Syntax], separator: &str) -> Syntax {
    let mut result = parts.to_vec();
    if !result.is_empty() {
        result.push(atom(separator));
    }
    result.push(atom("tail"));
    null(result)
}

fn first_sequence(terms: &[Syntax]) -> Syntax {
    Syntax::node(
        name("firstSequence"),
        vec![atom("firstSequence%["), separated(terms, ","), atom("]")],
    )
}

fn check_stops(macros: &BTreeMap<&str, CompiledMacro>) {
    let input = null(vec![atom("a"), atom("b"), atom("c")]);
    let state = MacroState::default();
    for (entry, expected) in [
        (
            "untypedSequenceMacro",
            separated(&[atom("a"), atom("b"), atom("c")], ","),
        ),
        (
            "appendSequenceMacro",
            appended(&[atom("a"), atom("b"), atom("c")], ","),
        ),
    ] {
        // The input fits this conversion allowance; only the larger returned
        // syntax exceeds it after native execution has completed.
        let bounded = macros[entry].execute(
            &input,
            &source(),
            &context(),
            &state,
            MacroLimits {
                syntax: SyntaxLimits {
                    max_nodes: 12,
                    ..SyntaxLimits::default()
                },
                ..MacroLimits::default()
            },
            None,
        );
        assert!(
            matches!(&bounded.outcome, Outcome::Inconclusive(reason) if matches!(reason.cause, InconclusiveCause::ResourceExhausted { .. })),
            "{bounded:?}"
        );
        assert!(
            bounded.vm_usage.is_some(),
            "output conversion must enforce the bound: {bounded:?}"
        );
        let exhausted = macros[entry].execute(
            &input,
            &source(),
            &context(),
            &state,
            MacroLimits {
                vm: ExecutionLimits {
                    max_steps: 0,
                    ..ExecutionLimits::default()
                },
                ..MacroLimits::default()
            },
            None,
        );
        assert!(
            matches!(&exhausted.outcome, Outcome::Inconclusive(reason) if matches!(reason.cause, InconclusiveCause::ResourceExhausted { .. })),
            "{exhausted:?}"
        );
        let cancelled = macros[entry].execute(
            &input,
            &source(),
            &context(),
            &state,
            MacroLimits::default(),
            Some(&|| true),
        );
        assert!(
            matches!(&cancelled.outcome, Outcome::Inconclusive(reason) if matches!(reason.cause, InconclusiveCause::Cancelled { .. })),
            "{cancelled:?}"
        );
        let recovered = macros[entry].execute(
            &input,
            &source(),
            &context(),
            &state,
            MacroLimits::default(),
            None,
        );
        assert!(
            matches!(recovered.outcome, Outcome::Complete(Ok(MacroResult::Expanded { syntax, state: next })) if syntax == expected && next == state)
        );
    }
}

fn check_generated_source(compiled: &CompiledMacro) {
    use fln_core::expr::{Expr, Literal, NatLit};
    use fln_env::constants::ConstantInfo;
    let limits = crate::EngineAdmissionLimits::new(crate::Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = crate::Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let options = crate::KVMap::new();
    let before = engine.logical_root(&options);
    for (terms, expected) in [
        (vec![], 42),
        (vec![number("7")], 7),
        (vec![number("7"), number("11"), number("13")], 7),
    ] {
        let report = compiled.execute(
            &first_sequence(&terms),
            &source(),
            &context(),
            &MacroState::default(),
            MacroLimits::default(),
            None,
        );
        let Outcome::Complete(Ok(MacroResult::Expanded { syntax, .. })) = report.outcome else {
            panic!("{report:?}");
        };
        let parsed =
            fln_parse::parse_definition(b"def nativeSequenceGenerated : Nat := 0").unwrap();
        let mut declaration = parsed.syntax().clone();
        let mut pending = vec![&mut declaration];
        let mut replacements = 0;
        while let Some(current) = pending.pop() {
            if current.kind() == Some(&name("num")) {
                *current = syntax.clone();
                replacements += 1;
            } else if let Syntax::Node { args, .. } = current {
                pending.extend(args.iter_mut());
            }
        }
        assert_eq!(replacements, 1);
        let candidate = fln_elab::elaborate_definition_in_with_budget(
            &declaration,
            engine.environment(),
            limits.kernel,
        )
        .unwrap();
        let admitted = engine
            .admit_declaration(candidate, &options, limits)
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(
            admitted.checker.ground,
            crate::CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
        let Some(ConstantInfo::Defn(definition)) = admitted
            .engine
            .environment()
            .find(&name("nativeSequenceGenerated"))
        else {
            panic!("generated sequence term was not admitted");
        };
        let verdict = fln_kernel::check_def_eq(
            admitted.engine.environment(),
            &[],
            &definition.value,
            &Expr::lit(Literal::Nat(NatLit::from_limbs_le(vec![expected]))),
            limits.kernel,
        );
        assert!(
            matches!(
                verdict,
                Outcome::Complete(fln_kernel::verdict::Verdict::Accepted { .. })
            ),
            "{verdict:?}"
        );
        assert_eq!(engine.logical_root(&options), before);
    }
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

fn lean_info(info: SourceInfo) -> String {
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

pub(super) fn lean_syntax(value: &Syntax) -> String {
    match value {
        Syntax::Missing => "Lean.Syntax.missing".into(),
        Syntax::Atom { info, val } => format!(
            "Lean.Syntax.atom ({}) {}",
            lean_info(*info),
            lean_string(val)
        ),
        Syntax::Node { info, kind, args } => format!(
            "Lean.Syntax.node ({}) ({}) #[{}]",
            lean_info(*info),
            lean_name(kind),
            args.iter()
                .map(|child| format!("({})", lean_syntax(child)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        Syntax::Ident {
            info,
            raw_val,
            val,
            preresolved,
        } => {
            let span = raw_val.span();
            let raw = format!(
                "⟨{}, ⟨{}⟩, ⟨{}⟩⟩",
                lean_string(raw_val.backing(&source())),
                span.start().0,
                span.end().0
            );
            let pre = preresolved
                .iter()
                .map(|entry| match entry {
                    Preresolved::Namespace { ns } => {
                        format!("Lean.Syntax.Preresolved.namespace ({})", lean_name(ns))
                    }
                    Preresolved::Decl { name, fields } => format!(
                        "Lean.Syntax.Preresolved.decl ({}) [{}]",
                        lean_name(name),
                        fields
                            .iter()
                            .map(|field| lean_string(field))
                            .collect::<Vec<_>>()
                            .join(", ")
                    ),
                })
                .collect::<Vec<_>>()
                .join(", ");
            format!(
                "Lean.Syntax.ident ({}) {raw} ({}) [{pre}]",
                lean_info(*info),
                lean_name(val)
            )
        }
    }
}

pub(super) const ORACLE: &str = r#"
def sameSequenceSubstring (a b : Substring.Raw) : Bool :=
  a.str == b.str && a.startPos == b.startPos && a.stopPos == b.stopPos
def sameSequenceInfo : Lean.SourceInfo → Lean.SourceInfo → Bool
  | .none, .none => true
  | .synthetic p q c, .synthetic p' q' c' => p == p' && q == q' && c == c'
  | .original l p t q, .original l' p' t' q' =>
    sameSequenceSubstring l l' && p == p' && sameSequenceSubstring t t' && q == q'
  | _, _ => false
partial def sameSequenceSyntax : Lean.Syntax → Lean.Syntax → Bool
  | .missing, .missing => true
  | .atom i s, .atom i' s' => sameSequenceInfo i i' && s == s'
  | .node i k a, .node i' k' a' =>
    sameSequenceInfo i i' && k == k' && a.isEqv a' sameSequenceSyntax
  | .ident i r n p, .ident i' r' n' p' =>
    sameSequenceInfo i i' && sameSequenceSubstring r r' && n == n' && p == p'
  | _, _ => false
def sequenceState : Lean.Macro.State :=
  ⟨23, [(`trace, "trace\x00λ")], [`previous, `older.expansion]⟩
def sameSequenceState (next : Lean.Macro.State) : Bool :=
  next.macroScope == sequenceState.macroScope && next.traceMsgs == sequenceState.traceMsgs &&
  next.expandedMacroDecls == sequenceState.expandedMacroDecls
def checkSequence (f : Lean.Syntax → Lean.MacroM Lean.Syntax)
    (input expected : Lean.Syntax) : Bool :=
  let ctx : Lean.Macro.Context := ⟨default, `Main, 17, 0, 512, input⟩
  match f input ctx sequenceState with
  | .ok value next => sameSequenceSyntax value expected && sameSequenceState next
  | _ => false
def checkSequenceUnsupported (f : Lean.Syntax → Lean.MacroM Lean.Syntax)
    (input : Lean.Syntax) : Bool :=
  let ctx : Lean.Macro.Context := ⟨default, `Main, 17, 0, 512, input⟩
  match f input ctx sequenceState with
  | .error .unsupportedSyntax next => sameSequenceState next
  | _ => false
"#;
