use super::*;
use crate::imported_macros::{MacroContext, MacroResult, MacroState, SyntaxLimits};
use fln_syntax::source::SourceText;
use fln_vm::interpreter::ExecutionLimits;

const CANDIDATES: [NativeTacticMacro; 4] = [
    NativeTacticMacro::ApplyRfl,
    NativeTacticMacro::EqRefl,
    NativeTacticMacro::ExactHEq,
    NativeTacticMacro::ExactIff,
];

fn span(start: usize, end: usize) -> ByteSpan {
    ByteSpan::new(BytePos(start), BytePos(end)).unwrap()
}

fn source() -> SourceText {
    SourceText::from_utf8(b"  rfl    ").unwrap()
}

fn atom(info: SourceInfo, text: &str) -> Syntax {
    Syntax::Atom {
        info,
        val: text.to_owned(),
    }
}

fn node(kind: &str, args: Vec<Syntax>) -> Syntax {
    Syntax::Node {
        info: SourceInfo::None,
        kind: name(kind),
        args,
    }
}

fn inputs() -> [Syntax; 3] {
    [
        node("Lean.Parser.Tactic.tacticRfl", Vec::new()),
        node(
            "Lean.Parser.Tactic.tacticRfl",
            vec![atom(SourceInfo::None, "wrong")],
        ),
        node(
            "Lean.Parser.Tactic.tacticRfl",
            vec![atom(SourceInfo::None, "rfl")],
        ),
    ]
}

fn references() -> [(Syntax, SourceInfo); 4] {
    let positioned = SourceInfo::Synthetic {
        pos: BytePos(2),
        end_pos: BytePos(5),
        canonical: true,
    };
    let expected = SourceInfo::Synthetic {
        pos: BytePos(2),
        end_pos: BytePos(5),
        canonical: false,
    };
    [
        (Syntax::Missing, SourceInfo::None),
        (atom(positioned, "rfl"), expected),
        (
            node(
                "container",
                vec![
                    Syntax::Missing,
                    atom(positioned, "first"),
                    atom(SourceInfo::None, "last"),
                ],
            ),
            expected,
        ),
        (
            node(
                "container",
                vec![atom(SourceInfo::None, "first"), atom(positioned, "last")],
            ),
            SourceInfo::None,
        ),
    ]
}

fn contexts() -> [MacroContext; 2] {
    [
        MacroContext {
            quotation_context: name("Client.Scope"),
            current_macro_scope: 17,
            current_recursion_depth: 3,
            max_recursion_depth: 512,
        },
        MacroContext {
            quotation_context: name("Other"),
            current_macro_scope: u64::MAX,
            current_recursion_depth: 0,
            max_recursion_depth: 512,
        },
    ]
}

fn state() -> MacroState {
    MacroState {
        macro_scope: 9,
        trace_messages: vec![(name("Trace"), "keep".to_owned())],
        expanded_macro_declarations: vec![name("Prior")],
    }
}

fn check_expansion(
    candidate: NativeTacticMacro,
    input: &Syntax,
    reference: &Syntax,
    context: &MacroContext,
    expected_info: SourceInfo,
) {
    let source = source();
    let state = state();
    let execution = candidate.execute(
        input,
        MacroInvocation {
            source: &source,
            context,
            state: &state,
            lookup: None,
        },
        MacroLimits::default(),
        None,
        Some(reference),
    );
    assert!(execution.reference_functions.is_empty());
    assert_eq!(execution.native_functions, vec![candidate.id()]);
    let usage = execution.vm_usage.unwrap();
    assert_eq!(usage.steps, 1);
    assert_eq!(usage.system_polls, 1);
    let Outcome::Complete(Ok(MacroResult::Expanded {
        syntax,
        state: next,
    })) = execution.outcome
    else {
        panic!("native {candidate:?}: {execution:?}");
    };
    assert_eq!(next, state, "a quotation does not allocate a fresh scope");
    let Syntax::Node { info, kind, args } = &syntax else {
        panic!("quotation is not a tactic node: {syntax:?}");
    };
    let (expected_kind, keyword, constant) = match candidate {
        NativeTacticMacro::ApplyRfl => ("applyRfl", "apply_rfl", None),
        NativeTacticMacro::EqRefl => ("eqRefl", "eq_refl", None),
        NativeTacticMacro::ExactHEq => ("exact", "exact", Some("HEq.rfl")),
        NativeTacticMacro::ExactIff => ("exact", "exact", Some("Iff.rfl")),
        other => panic!("not a reflexivity candidate: {other:?}"),
    };
    assert_eq!(*info, expected_info);
    assert_eq!(*kind, Name::str(name("Lean.Parser.Tactic"), expected_kind));
    assert_eq!(args[0], atom(expected_info, keyword));
    assert_eq!(args.len(), if constant.is_some() { 2 } else { 1 });
    if let Some(constant) = constant {
        let Syntax::Ident {
            info,
            raw_val,
            val,
            preresolved,
        } = &args[1]
        else {
            panic!("exact quotation lost its identifier: {:?}", args[1]);
        };
        assert_eq!(*info, expected_info);
        assert_eq!(raw_val.owned_backing(), Some(constant));
        assert_eq!(raw_val.text(&source), Some(constant));
        assert_eq!(raw_val.span(), span(0, 7));
        assert_eq!(raw_val.source_span(), None);
        // Construct the known no-prior-scope spelling independently of the
        // native add_macro_scope helper used by production.
        let scope_context = Name::str(name(constant), "_@").append_core(&context.quotation_context);
        assert_eq!(
            *val,
            Name::num(
                Name::str(scope_context, "_hyg"),
                context.current_macro_scope
            )
        );
        assert_eq!(
            preresolved,
            &[Preresolved::Decl {
                name: name(constant),
                fields: Vec::new(),
            }]
        );
    }
}

#[test]
fn native_rfl_quotes_preserve_owned_raw_bytes_hygiene_reference_and_state() {
    for candidate in CANDIDATES {
        for context in contexts() {
            for (reference, expected) in references() {
                for input in inputs() {
                    check_expansion(candidate, &input, &reference, &context, expected);
                }
            }
        }
    }
}

#[test]
fn native_rfl_names_have_no_authority_without_the_verified_partition() {
    let unclassified = VerifiedPartition::user_fixture();
    for candidate in NativeTacticMacro::ALL {
        assert_eq!(
            NativeTacticMacro::identify(
                &name(candidate.module()),
                &name(candidate.declaration()),
                &unclassified,
            ),
            None
        );
    }
}

#[test]
fn native_rfl_unsupported_and_resource_stops_preserve_recovery() {
    let source = source();
    let state = state();
    let context = contexts()[0].clone();
    for candidate in CANDIDATES {
        for input in [
            Syntax::Missing,
            atom(SourceInfo::None, "rfl"),
            node("User.tacticRfl", Vec::new()),
        ] {
            let result = candidate.execute(
                &input,
                MacroInvocation {
                    source: &source,
                    context: &context,
                    state: &state,
                    lookup: None,
                },
                MacroLimits::default(),
                None,
                None,
            );
            assert!(matches!(result.outcome,
                Outcome::Complete(Ok(MacroResult::Unsupported { state: next })) if next == state));
        }
        for limits in [
            MacroLimits {
                vm: ExecutionLimits {
                    max_steps: 0,
                    ..ExecutionLimits::default()
                },
                ..MacroLimits::default()
            },
            MacroLimits {
                vm: ExecutionLimits {
                    max_stack_depth: 0,
                    ..ExecutionLimits::default()
                },
                ..MacroLimits::default()
            },
            MacroLimits {
                syntax: SyntaxLimits {
                    max_nodes: 0,
                    ..SyntaxLimits::default()
                },
                ..MacroLimits::default()
            },
            MacroLimits {
                syntax: SyntaxLimits {
                    max_bytes: 1,
                    ..SyntaxLimits::default()
                },
                ..MacroLimits::default()
            },
        ] {
            let result = candidate.execute(
                &inputs()[0],
                MacroInvocation {
                    source: &source,
                    context: &context,
                    state: &state,
                    lookup: None,
                },
                limits,
                None,
                None,
            );
            assert!(
                matches!(result.outcome, Outcome::Inconclusive(_)),
                "{result:?}"
            );
        }
        let cancelled = candidate.execute(
            &inputs()[0],
            MacroInvocation {
                source: &source,
                context: &context,
                state: &state,
                lookup: None,
            },
            MacroLimits::default(),
            Some(&|| true),
            None,
        );
        assert!(matches!(cancelled.outcome, Outcome::Inconclusive(_)));
        check_expansion(
            candidate,
            &inputs()[0],
            &Syntax::Missing,
            &context,
            SourceInfo::None,
        );
    }
}

#[test]
fn live_pinned_rfl_candidates_match_every_quotation_field() {
    use std::path::PathBuf;
    use std::process::Command;

    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for native rfl quotation comparison"
        );
        eprintln!("SKIP: native rfl quotations require FLN_REFERENCE_LEAN");
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
    let partition_path = std::env::var_os("FLN_REFERENCE_PARTITION")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            fln_core::checked_workspace_root!().join("contracts/builtin_partition.tsv")
        });
    let partition =
        VerifiedPartition::from_pinned_tsv(&std::fs::read_to_string(partition_path).unwrap())
            .unwrap();
    for candidate in CANDIDATES {
        assert_eq!(
            NativeTacticMacro::identify(
                &name(candidate.module()),
                &name(candidate.declaration()),
                &partition,
            ),
            Some(candidate)
        );
        for (module, declaration) in [
            (name("User"), name(candidate.declaration())),
            (
                name(candidate.module()),
                if candidate.declaration().contains('.') {
                    Name::str(Name::anonymous(), candidate.declaration())
                } else {
                    // Init.Core's generated name is already one component;
                    // flattening it would leave its identity unchanged.
                    Name::str(name(candidate.declaration()), "other")
                },
            ),
            (
                name(candidate.module()),
                Name::str(name(candidate.declaration()), "_redArg"),
            ),
        ] {
            assert_eq!(
                NativeTacticMacro::identify(&module, &declaration, &partition),
                None
            );
        }
    }
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!("native-rfl-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(
        dir.join("NativeRflMacros.lean"),
        include_str!("../../../../fln-olean/fixtures/NativeRflMacros.lean"),
    )
    .unwrap();
    let result = Command::new(&reference)
        .current_dir(&dir)
        .args(["-j1", "NativeRflMacros.lean"])
        .output()
        .unwrap();
    std::fs::write(dir.join("oracle.stdout"), &result.stdout).unwrap();
    std::fs::write(dir.join("oracle.stderr"), &result.stderr).unwrap();
    assert!(
        result.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
    let mut cases = 0;
    for candidate in CANDIDATES {
        for context in contexts() {
            for (reference, expected) in references() {
                for input in inputs() {
                    check_expansion(candidate, &input, &reference, &context, expected);
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 96);
    let expected = format!(
        "[{}]\n[{}]\n",
        vec!["true"; cases].join(", "),
        ["true"; 12].join(", "),
    );
    assert_eq!(
        String::from_utf8(result.stdout).unwrap(),
        expected,
        "{dir:?}"
    );
    assert!(result.stderr.is_empty());
    eprintln!("native and pinned rfl candidates: 96 exact quotations, 12 unsupported inputs");
}

const CONTROL_CANDIDATES: [NativeTacticMacro; 4] = [
    NativeTacticMacro::Exfalso,
    NativeTacticMacro::InferInstance,
    NativeTacticMacro::Try,
    NativeTacticMacro::NoFun,
];

fn control_body() -> Syntax {
    node(
        "Client.body",
        vec![
            Syntax::Ident {
                info: SourceInfo::Original {
                    leading: span(0, 2),
                    pos: BytePos(2),
                    trailing: span(5, 9),
                    end_pos: BytePos(5),
                },
                raw_val: RawIdentifier::owned(Arc::from("prefix::local::suffix"), span(8, 13))
                    .unwrap(),
                val: Name::num(name("Captured._hyg"), 23),
                preresolved: vec![
                    Preresolved::Namespace { ns: name("Imported") },
                    Preresolved::Decl {
                        name: name("Target"),
                        fields: vec!["field".to_owned()],
                    },
                ],
            },
            Syntax::Missing,
            atom(
                SourceInfo::Synthetic {
                    pos: BytePos(2),
                    end_pos: BytePos(5),
                    canonical: false,
                },
                "λ",
            ),
        ],
    )
}

fn control_inputs(candidate: NativeTacticMacro) -> [Syntax; 4] {
    let kind = format!("Lean.Parser.Tactic.{}", candidate.input_kind());
    [
        node(&kind, Vec::new()),
        node(&kind, vec![atom(SourceInfo::None, "wrong")]),
        node(&kind, vec![atom(SourceInfo::None, "wrong"), control_body()]),
        node(
            &kind,
            vec![
                atom(SourceInfo::None, "wrong"),
                Syntax::Missing,
                atom(SourceInfo::None, "extra"),
            ],
        ),
    ]
}

fn control_execute(
    candidate: NativeTacticMacro,
    input: &Syntax,
    context: &MacroContext,
    reference: &Syntax,
    limits: MacroLimits,
    cancellation: Option<&dyn CancellationProbe>,
) -> MacroExecution {
    candidate.execute(
        input,
        MacroInvocation {
            source: &source(),
            context,
            state: &state(),
            lookup: None,
        },
        limits,
        cancellation,
        Some(reference),
    )
}

fn expanded_control(candidate: NativeTacticMacro, input: &Syntax) -> Syntax {
    let execution = control_execute(
        candidate,
        input,
        &contexts()[0],
        &Syntax::Missing,
        MacroLimits::default(),
        None,
    );
    assert!(execution.reference_functions.is_empty());
    assert_eq!(execution.native_functions, vec![candidate.id()]);
    assert_eq!(execution.vm_usage.unwrap().steps, 1);
    let Outcome::Complete(Ok(MacroResult::Expanded { syntax, state: next })) = execution.outcome
    else {
        panic!("native {candidate:?}: {execution:?}");
    };
    assert_eq!(next, state());
    syntax
}

#[test]
fn native_try_keeps_captured_syntax_and_caller_hygiene_intact() {
    let candidate = NativeTacticMacro::Try;
    let output = expanded_control(candidate, &control_inputs(candidate)[2]);
    let mut pending = vec![&output];
    let mut captured = Vec::new();
    while let Some(syntax) = pending.pop() {
        if syntax.kind() == Some(&name("Client.body")) {
            captured.push(syntax);
        }
        if let Syntax::Node { args, .. } = syntax {
            pending.extend(args);
        }
    }
    assert_eq!(captured, vec![&control_body()]);
    // A quotation splices the whole tactic sequence once. It neither re-parses
    // its raw bytes nor gives its identifiers the quotation's new macro scope.
    assert_eq!(
        expanded_control(candidate, &control_inputs(candidate)[0]),
        expanded_control(candidate, &control_inputs(candidate)[3]),
        "a missing capture is Syntax.missing, and extra children are ignored"
    );
}

#[test]
fn native_control_macros_preserve_refusals_limits_and_recovery() {
    for candidate in CONTROL_CANDIDATES {
        let input = control_inputs(candidate)[2].clone();
        let baseline = expanded_control(candidate, &input);
        for invalid in [
            Syntax::Missing,
            atom(SourceInfo::None, "wrong"),
            node("User.tactic", Vec::new()),
        ] {
            let execution = control_execute(
                candidate,
                &invalid,
                &contexts()[0],
                &Syntax::Missing,
                MacroLimits::default(),
                None,
            );
            assert!(matches!(execution.outcome,
                Outcome::Complete(Ok(MacroResult::Unsupported { state: next })) if next == state()));
        }
        for limits in [
            MacroLimits {
                vm: ExecutionLimits { max_steps: 0, ..ExecutionLimits::default() },
                ..MacroLimits::default()
            },
            MacroLimits {
                vm: ExecutionLimits { max_stack_depth: 0, ..ExecutionLimits::default() },
                ..MacroLimits::default()
            },
            MacroLimits {
                syntax: SyntaxLimits { max_nodes: 2, ..SyntaxLimits::default() },
                ..MacroLimits::default()
            },
            MacroLimits {
                syntax: SyntaxLimits { max_bytes: 32, ..SyntaxLimits::default() },
                ..MacroLimits::default()
            },
        ] {
            let execution = control_execute(
                candidate,
                &input,
                &contexts()[0],
                &Syntax::Missing,
                limits,
                None,
            );
            assert!(matches!(execution.outcome, Outcome::Inconclusive(_)), "{execution:?}");
        }
        let cancelled = control_execute(
            candidate,
            &input,
            &contexts()[0],
            &Syntax::Missing,
            MacroLimits::default(),
            Some(&|| true),
        );
        assert!(matches!(cancelled.outcome, Outcome::Inconclusive(_)));
        let malformed = atom(
            SourceInfo::Original {
                leading: span(0, 2),
                pos: BytePos(2),
                trailing: span(10, 10),
                end_pos: BytePos(10),
            },
            "invalid reference",
        );
        let rejected = control_execute(
            candidate,
            &input,
            &contexts()[0],
            &malformed,
            MacroLimits::default(),
            None,
        );
        assert!(matches!(rejected.outcome,
            Outcome::Complete(Err(super::super::MacroExecutionError::Conversion(_)))));
        assert_eq!(expanded_control(candidate, &input), baseline);
    }
}

fn control_text(text: &str) -> String {
    format!("{}:{text}", text.len())
}

fn control_name(value: &Name) -> String {
    use fln_core::name::LeafView;
    match value.leaf_view() {
        LeafView::Anonymous => "a".to_owned(),
        LeafView::Str(component) => {
            format!("s{}{}", control_name(&value.parent()), control_text(component))
        }
        LeafView::Num(component) => format!("u{}{component};", control_name(&value.parent())),
    }
}

fn control_raw(backing: &str, span: ByteSpan) -> String {
    format!("{}{},{};", control_text(backing), span.start().0, span.end().0)
}

fn control_info(info: SourceInfo) -> String {
    match info {
        SourceInfo::None => "-".to_owned(),
        SourceInfo::Synthetic { pos, end_pos, canonical } => {
            format!("s{},{},{};", pos.0, end_pos.0, u8::from(canonical))
        }
        SourceInfo::Original { leading, pos, trailing, end_pos } => format!(
            "o{}{};{}{};",
            control_raw(source().as_str(), leading),
            pos.0,
            control_raw(source().as_str(), trailing),
            end_pos.0,
        ),
    }
}

fn control_syntax(syntax: &Syntax) -> String {
    match syntax {
        Syntax::Missing => "m".to_owned(),
        Syntax::Node { info, kind, args } => format!(
            "N{}{}[{}]",
            control_info(*info),
            control_name(kind),
            args.iter().map(control_syntax).collect::<String>(),
        ),
        Syntax::Atom { info, val } => format!("A{}{}", control_info(*info), control_text(val)),
        Syntax::Ident { info, raw_val, val, preresolved } => format!(
            "I{}{}{}[{}]",
            control_info(*info),
            control_raw(raw_val.backing(&source()), raw_val.span()),
            control_name(val),
            preresolved.iter().map(|entry| match entry {
                Preresolved::Namespace { ns } => format!("n{}", control_name(ns)),
                Preresolved::Decl { name, fields } => format!(
                    "d{}[{}]",
                    control_name(name),
                    fields.iter().map(|field| control_text(field)).collect::<String>(),
                ),
            }).collect::<String>(),
        ),
    }
}

#[test]
fn live_pinned_control_candidates_match_complete_quotations_and_state() {
    use std::path::PathBuf;
    use std::process::Command;

    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for native control macro comparison");
        eprintln!("SKIP: native control quotations require FLN_REFERENCE_LEAN");
        return;
    };
    let version = Command::new(&reference).args(["-j1", "--githash"]).output().unwrap();
    assert!(version.status.success());
    assert_eq!(String::from_utf8(version.stdout).unwrap().trim(), fln_olean::format::PIN_COMMIT);
    let partition_path = std::env::var_os("FLN_REFERENCE_PARTITION")
        .map(PathBuf::from)
        .unwrap_or_else(|| fln_core::checked_workspace_root!().join("contracts/builtin_partition.tsv"));
    let partition = VerifiedPartition::from_pinned_tsv(
        &std::fs::read_to_string(partition_path).unwrap(),
    ).unwrap();
    for candidate in CONTROL_CANDIDATES {
        assert_eq!(NativeTacticMacro::identify(
            &name(candidate.module()), &name(candidate.declaration()), &partition,
        ), Some(candidate));
        for (module, declaration) in [
            (name("User"), name(candidate.declaration())),
            (name(candidate.module()), Name::str(Name::anonymous(), candidate.declaration())),
            (name(candidate.module()), Name::str(name(candidate.declaration()), "_redArg")),
        ] {
            assert_eq!(NativeTacticMacro::identify(&module, &declaration, &partition), None);
        }
    }
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from).unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    let dir = root.join(format!("native-control-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("NativeControlMacros.lean"),
        include_str!("../../../../fln-olean/fixtures/NativeControlMacros.lean")).unwrap();
    let result = Command::new(&reference).current_dir(&dir)
        .args(["-j1", "NativeControlMacros.lean"]).output().unwrap();
    std::fs::write(dir.join("oracle.stdout"), &result.stdout).unwrap();
    std::fs::write(dir.join("oracle.stderr"), &result.stderr).unwrap();
    assert!(result.status.success(), "{dir:?}: {}{}",
        String::from_utf8_lossy(&result.stdout), String::from_utf8_lossy(&result.stderr));
    let mut native = String::new();
    let mut cases = 0;
    for candidate in CONTROL_CANDIDATES {
        for context in contexts() {
            for (reference, _) in references() {
                for input in control_inputs(candidate) {
                    let execution = control_execute(candidate, &input, &context, &reference,
                        MacroLimits::default(), None);
                    assert!(execution.reference_functions.is_empty());
                    assert_eq!(execution.native_functions, vec![candidate.id()]);
                    let Outcome::Complete(Ok(MacroResult::Expanded { syntax, state: next })) = execution.outcome
                    else { panic!("{execution:?}"); };
                    native.push_str(&format!("ok:{}:{}\n", control_syntax(&syntax), next == state()));
                    cases += 1;
                }
            }
        }
        for input in [Syntax::Missing, atom(SourceInfo::None, "wrong"), node("User.tactic", vec![])] {
            let execution = control_execute(candidate, &input, &contexts()[0], &Syntax::Missing,
                MacroLimits::default(), None);
            let Outcome::Complete(Ok(MacroResult::Unsupported { state: next })) = execution.outcome
            else { panic!("{execution:?}"); };
            native.push_str(&format!("unsupported:{}\n", next == state()));
        }
    }
    assert_eq!(cases, 128);
    std::fs::write(dir.join("native.stdout"), &native).unwrap();
    assert_eq!(String::from_utf8(result.stdout).unwrap(), native, "{dir:?}");
    assert!(result.stderr.is_empty());
    eprintln!("native and pinned control macros: 128 exact quotations, 12 unsupported inputs");
}
