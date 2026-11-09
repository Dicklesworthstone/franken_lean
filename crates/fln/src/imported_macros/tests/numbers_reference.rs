//! Numeric literal APIs through actual user MacroM IR and the hash-verified
//! partition, including arbitrary Nat values and the generated-term consumer.
use super::*;
use fln_core::name::LeafView;
use std::{collections::BTreeMap, path::PathBuf, process::Command};

const TWO_64: &str = "18446744073709551616";
const TWO_128: &str = "340282366920938463463374607431768211456";
const HUGE_NAT: &str =
    "115792089237316195423570985008687907853269984665640564039457584007913129639937";

#[test]
fn live_pinned_numeric_literals_preserve_arbitrary_nats_state_and_native_provenance() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from);
    let partition = std::env::var_os("FLN_REFERENCE_PARTITION").map(PathBuf::from);
    let (Some(reference), Some(partition)) = (reference, partition) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference and verified partition required for numeric literal macros"
        );
        eprintln!(
            "SKIP: numeric literal macros require FLN_REFERENCE_LEAN and FLN_REFERENCE_PARTITION"
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
        .join(format!("num-macro-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let fixture = include_str!("../../../../fln-olean/fixtures/ir/NumMacroModule.lean");
    std::fs::write(dir.join("NumMacroModule.lean"), fixture).unwrap();
    let emitted = Command::new(&reference)
        .current_dir(&dir)
        .args(["-j1", "-o", "NumMacroModule.olean", "NumMacroModule.lean"])
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
        &std::fs::read(dir.join("NumMacroModule.ir")).unwrap(),
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
    let macros: BTreeMap<_, _> = [
        "spelledNumberMacro",
        "normalizeNumberMacro",
        "typedNumberMacro",
        "quotedNumberMacro",
        "hugeNaturalMacro",
        "expandNumIncrement",
    ]
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
    for info in infos() {
        // mkNumLit deliberately preserves a spelling, even when it is not a
        // source numeral. Consumers below must make their own decoding choice.
        for spelling in ["", "0", "001_2", "0xF", "0b102", "1__2", "0_1", " λ🙂\0"] {
            cases.push((
                "spelledNumberMacro",
                Syntax::Atom {
                    info,
                    val: spelling.into(),
                },
                lit(spelling, info),
            ));
        }
        cases.push((
            "hugeNaturalMacro",
            Syntax::Atom {
                info,
                val: "ignored".into(),
            },
            lit(HUGE_NAT, info),
        ));
    }
    for (index, (spelling, decoded)) in numeric_spellings().into_iter().enumerate() {
        let info = infos()[index % infos().len()];
        let input = lit(spelling, info);
        cases.push((
            "normalizeNumberMacro",
            input.clone(),
            decoded.map_or(Syntax::Missing, |value| lit(value, info)),
        ));
        cases.push((
            "typedNumberMacro",
            input.clone(),
            lit(decoded.unwrap_or("0"), info),
        ));
        cases.push((
            "quotedNumberMacro",
            input,
            lit(decoded.unwrap_or("0"), SourceInfo::None),
        ));
    }
    for (spelling, incremented) in [
        ("0", "1"),
        ("41", "42"),
        ("0xff", "256"),
        ("0b1111", "16"),
        ("0o77", "64"),
        ("18446744073709551615", TWO_64),
        (TWO_64, "18446744073709551617"),
        ("0xffffffffffffffffffffffffffffffff", TWO_128),
        ("1__2", "13"),
        ("0x", "1"),
        ("0_1", "1"),
    ] {
        cases.push((
            "expandNumIncrement",
            increment_input(spelling),
            lit(incremented, SourceInfo::None),
        ));
    }
    for input in [
        Syntax::Missing,
        atom("num"),
        Syntax::node(name("num"), vec![]),
        Syntax::node(name("num"), vec![atom("1"), atom("2")]),
        Syntax::node(name("num"), vec![Syntax::Missing]),
        Syntax::node(name("num"), vec![lit("7", SourceInfo::None)]),
        Syntax::node(name("Lean.num"), vec![atom("7")]),
    ] {
        cases.push(("normalizeNumberMacro", input.clone(), Syntax::Missing));
        cases.push((
            "typedNumberMacro",
            input.clone(),
            lit("0", SourceInfo::None),
        ));
        cases.push(("quotedNumberMacro", input, lit("0", SourceInfo::None)));
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
            "only this user module may execute interpreted IR: {entry}"
        );
        let Outcome::Complete(Ok(MacroResult::Expanded {
            syntax,
            state: next,
        })) = report.outcome
        else {
            panic!("{entry} on {input:?}: {:?}; {dir:?}", report.outcome);
        };
        assert_eq!(syntax, *expected, "{entry} on {input:?}");
        assert_eq!(next, state, "all three state fields must survive {entry}");
        checks.push(format!(
            "checkNumber {entry} ({}) ({})",
            lean_syntax(input),
            lean_syntax(expected)
        ));
    }
    for helper in [
        "Lean.Syntax.mkNumLit",
        "Lean.Syntax.mkNatLit",
        "Lean.Syntax.isNatLit?",
        "Lean.TSyntax.getNat",
        "Nat.reprFast",
    ] {
        assert!(
            rows.contains(&format!("mirror:{helper}")),
            "actual user IR missed {helper}"
        );
    }
    let unsupported = macros["expandNumIncrement"].execute(
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
    check_stops(&macros["hugeNaturalMacro"]);
    check_native_magnitude_stops(&macros);
    check_generated_source(&macros);
    let oracle = format!(
        "{fixture}\n{ORACLE}\n#eval ([{}] : List Bool).all id\n",
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
        "native and pinned numeric literal macros: {} complete syntax/state cases plus generated-source admission",
        checks.len()
    );
}

fn numeric_spellings() -> Vec<(&'static str, Option<&'static str>)> {
    vec![
        ("0", Some("0")),
        ("7", Some("7")),
        ("000", Some("0")),
        ("001_2", Some("12")),
        ("1__2", Some("12")),
        ("1_", Some("1")),
        ("1____", Some("1")),
        ("12_34", Some("1234")),
        ("00_", Some("0")),
        ("0x", Some("0")),
        ("0X", Some("0")),
        ("0x_", Some("0")),
        ("0b", Some("0")),
        ("0b_", Some("0")),
        ("0o", Some("0")),
        ("0o_", Some("0")),
        ("0x_f_", Some("15")),
        ("0XfF", Some("255")),
        ("0B101__0_", Some("10")),
        ("0O7_7", Some("63")),
        ("18446744073709551615", Some("18446744073709551615")),
        (TWO_64, Some(TWO_64)),
        ("0x10000000000000000", Some(TWO_64)),
        (
            "0xffffffffffffffffffffffffffffffff",
            Some("340282366920938463463374607431768211455"),
        ),
        (
            "0b10000000000000000000000000000000000000000000000000000000000000000",
            Some(TWO_64),
        ),
        ("0o2000000000000000000000", Some(TWO_64)),
        (HUGE_NAT, Some(HUGE_NAT)),
        ("", None),
        ("_", None),
        ("_1", None),
        ("0_", None),
        ("0__", None),
        ("0_1", None),
        ("0xG", None),
        ("0b2", None),
        ("0o8", None),
        ("0x1z", None),
        ("-1", None),
        ("+1", None),
        (" 1", None),
        ("1 ", None),
        ("1.0", None),
        ("1e2", None),
        ("١", None),
        ("٠1", None),
        ("１", None),
        ("1λ", None),
        ("0λ", None),
        ("0xλ", None),
        ("0\0", None),
        ("1\n", None),
    ]
}

fn infos() -> [SourceInfo; 3] {
    [
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
    ]
}

fn atom(text: &str) -> Syntax {
    Syntax::Atom {
        info: SourceInfo::None,
        val: text.into(),
    }
}

fn lit(text: &str, info: SourceInfo) -> Syntax {
    Syntax::node(
        name("num"),
        vec![Syntax::Atom {
            info,
            val: text.into(),
        }],
    )
}

fn increment_input(text: &str) -> Syntax {
    Syntax::node(
        name("numIncrement"),
        vec![atom("numIncrement%"), lit(text, SourceInfo::None)],
    )
}

fn check_stops(compiled: &CompiledMacro) {
    let input = atom("x");
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
            "only the expanded result must exceed this allowance"
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
        matches!(report.outcome, Outcome::Complete(Ok(MacroResult::Expanded { syntax, state: next })) if syntax == lit(HUGE_NAT, SourceInfo::None) && next == state)
    );
}

fn check_native_magnitude_stops(macros: &BTreeMap<&str, CompiledMacro>) {
    let input = lit(TWO_64, SourceInfo::None);
    let state = MacroState::default();
    for (entry, row) in [
        ("normalizeNumberMacro", "mirror:Lean.Syntax.isNatLit?"),
        ("typedNumberMacro", "mirror:Lean.TSyntax.getNat"),
    ] {
        // Ingress contains only a String; no oversized IR Nat constant or
        // syntax conversion can consume this execution-only magnitude bound.
        let limited = macros[entry].execute(
            &input,
            &source(),
            &context(),
            &state,
            MacroLimits {
                vm: ExecutionLimits {
                    max_nat_magnitude_bytes: 8,
                    ..ExecutionLimits::default()
                },
                ..MacroLimits::default()
            },
            None,
        );
        assert!(limited.native_functions.iter().any(|name| name == row));
        let Outcome::Inconclusive(reason) = &limited.outcome else {
            panic!("native Nat decoding must preserve its resource stop: {limited:?}");
        };
        assert!(
            matches!(&reason.cause, InconclusiveCause::ResourceExhausted { usage }
                if usage.allowed == 8 && usage.observed == 16
                    && usage.reason == (fln_core::diag::ResourceReason::Memory { limit_bytes: 8 })),
            "{limited:?}"
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
            matches!(recovered.outcome, Outcome::Complete(Ok(MacroResult::Expanded { syntax, state: next }))
                if syntax == input && next == state)
        );
    }
}

fn check_generated_source(macros: &BTreeMap<&str, CompiledMacro>) {
    use fln_core::expr::{Expr, Literal, NatLit};
    use fln_env::constants::ConstantInfo;
    let limits = crate::EngineAdmissionLimits::new(crate::Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = crate::Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let options = crate::KVMap::new();
    let before = engine.logical_root(&options);
    for (entry, input, limbs) in [
        ("expandNumIncrement", increment_input("0xff"), vec![256]),
        (
            "expandNumIncrement",
            increment_input("18446744073709551615"),
            vec![0, 1],
        ),
        ("expandNumIncrement", increment_input(TWO_64), vec![1, 1]),
        ("hugeNaturalMacro", atom("x"), vec![1, 0, 0, 0, 1]),
        ("spelledNumberMacro", atom("0x"), Vec::new()),
        ("typedNumberMacro", lit("0_1", SourceInfo::None), Vec::new()),
    ] {
        let report = macros[entry].execute(
            &input,
            &source(),
            &context(),
            &MacroState::default(),
            MacroLimits::default(),
            None,
        );
        let Outcome::Complete(Ok(MacroResult::Expanded { syntax, .. })) = report.outcome else {
            panic!("{report:?}");
        };
        let declaration = generated_definition(syntax);
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
            .find(&name("nativeNumberGenerated"))
        else {
            panic!("generated numeral was not admitted");
        };
        let verdict = fln_kernel::check_def_eq(
            admitted.engine.environment(),
            &[],
            &definition.value,
            &Expr::lit(Literal::Nat(NatLit::from_limbs_le(limbs))),
            limits.kernel,
        );
        assert!(
            matches!(
                verdict,
                Outcome::Complete(fln_kernel::verdict::Verdict::Accepted { .. })
            ),
            "{entry}: {verdict:?}"
        );
        assert_eq!(engine.logical_root(&options), before);
    }
    // mkNumLit can construct this token, but it is not a valid natural value.
    // The source consumer must reject it; getNat's explicit default above is
    // the only route by which this malformed spelling becomes the value zero.
    let report = macros["spelledNumberMacro"].execute(
        &atom("0_1"),
        &source(),
        &context(),
        &MacroState::default(),
        MacroLimits::default(),
        None,
    );
    let Outcome::Complete(Ok(MacroResult::Expanded { syntax, .. })) = report.outcome else {
        panic!("{report:?}");
    };
    assert!(
        fln_elab::elaborate_definition_in_with_budget(
            &generated_definition(syntax),
            engine.environment(),
            limits.kernel
        )
        .is_err()
    );
    assert_eq!(engine.logical_root(&options), before);
}

fn generated_definition(value: Syntax) -> Syntax {
    let parsed = fln_parse::parse_definition(b"def nativeNumberGenerated : Nat := 0").unwrap();
    let mut syntax = parsed.syntax().clone();
    let mut pending = vec![&mut syntax];
    let mut replacements = 0;
    while let Some(current) = pending.pop() {
        if current.kind() == Some(&name("num")) {
            *current = value.clone();
            replacements += 1;
        } else if let Syntax::Node { args, .. } = current {
            pending.extend(args.iter_mut());
        }
    }
    assert_eq!(replacements, 1);
    syntax
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
        Syntax::Ident { .. } => panic!("numeric fixture does not construct identifiers"),
    }
}

const ORACLE: &str = r#"
def sameNumberSubstring (a b : Substring.Raw) : Bool :=
  a.str == b.str && a.startPos == b.startPos && a.stopPos == b.stopPos
def sameNumberInfo : Lean.SourceInfo → Lean.SourceInfo → Bool
  | .none, .none => true
  | .synthetic p q c, .synthetic p' q' c' => p == p' && q == q' && c == c'
  | .original l p t q, .original l' p' t' q' =>
    sameNumberSubstring l l' && p == p' && sameNumberSubstring t t' && q == q'
  | _, _ => false
partial def sameNumberSyntax : Lean.Syntax → Lean.Syntax → Bool
  | .missing, .missing => true
  | .atom i s, .atom i' s' => sameNumberInfo i i' && s == s'
  | .node i k a, .node i' k' a' =>
    sameNumberInfo i i' && k == k' && a.isEqv a' sameNumberSyntax
  | _, _ => false
def checkNumber (f : Lean.Syntax → Lean.MacroM Lean.Syntax)
    (input expected : Lean.Syntax) : Bool :=
  let ctx : Lean.Macro.Context := ⟨default, `Main, 17, 0, 512, input⟩
  let state : Lean.Macro.State :=
    ⟨23, [(`trace, "trace\x00λ")], [`previous, `older.expansion]⟩
  match f input ctx state with
  | .ok value next => sameNumberSyntax value expected && next.macroScope == state.macroScope &&
    next.traceMsgs == state.traceMsgs && next.expandedMacroDecls == state.expandedMacroDecls
  | _ => false
"#;
