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
                    Preresolved::Namespace {
                        ns: name("Imported"),
                    },
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
    let Outcome::Complete(Ok(MacroResult::Expanded {
        syntax,
        state: next,
    })) = execution.outcome
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
    let candidates = CONTROL_CANDIDATES
        .into_iter()
        .map(|candidate| (candidate, control_inputs(candidate)[2].clone()))
        .chain(COMPOSITE_CANDIDATES.into_iter().map(|candidate| {
            let input = composite_inputs(candidate).pop().unwrap();
            (candidate, input)
        }))
        .chain(SEQUENCING_CANDIDATES.into_iter().map(|candidate| {
            let input = sequencing_inputs(candidate).swap_remove(3);
            (candidate, input)
        }))
        .chain(OPERATOR_CANDIDATES.into_iter().map(|candidate| {
            let input = operator_inputs(candidate).swap_remove(3);
            (candidate, input)
        }))
        .chain(BINDER_CANDIDATES.into_iter().map(|candidate| {
            let input = binder_inputs(candidate).swap_remove(3);
            (candidate, input)
        }));
    for (candidate, input) in candidates {
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
            assert!(matches!(
                execution.outcome,
                Outcome::Complete(Ok(MacroResult::Unsupported { state: next })) if next == state()
            ));
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
                    max_nodes: 2,
                    ..SyntaxLimits::default()
                },
                ..MacroLimits::default()
            },
            MacroLimits {
                syntax: SyntaxLimits {
                    max_bytes: 32,
                    ..SyntaxLimits::default()
                },
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
            assert!(
                matches!(execution.outcome, Outcome::Inconclusive(_)),
                "{execution:?}"
            );
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
        assert!(matches!(
            rejected.outcome,
            Outcome::Complete(Err(super::super::MacroExecutionError::Conversion(_)))
        ));
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
            format!(
                "s{}{}",
                control_name(&value.parent()),
                control_text(component)
            )
        }
        LeafView::Num(component) => format!("u{}{component};", control_name(&value.parent())),
    }
}

fn control_raw(backing: &str, span: ByteSpan) -> String {
    format!(
        "{}{},{};",
        control_text(backing),
        span.start().0,
        span.end().0
    )
}

fn control_info(info: SourceInfo) -> String {
    match info {
        SourceInfo::None => "-".to_owned(),
        SourceInfo::Synthetic {
            pos,
            end_pos,
            canonical,
        } => {
            format!("s{},{},{};", pos.0, end_pos.0, u8::from(canonical))
        }
        SourceInfo::Original {
            leading,
            pos,
            trailing,
            end_pos,
        } => format!(
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
        Syntax::Ident {
            info,
            raw_val,
            val,
            preresolved,
        } => format!(
            "I{}{}{}[{}]",
            control_info(*info),
            control_raw(raw_val.backing(&source()), raw_val.span()),
            control_name(val),
            preresolved
                .iter()
                .map(|entry| match entry {
                    Preresolved::Namespace { ns } => format!("n{}", control_name(ns)),
                    Preresolved::Decl { name, fields } => format!(
                        "d{}[{}]",
                        control_name(name),
                        fields
                            .iter()
                            .map(|field| control_text(field))
                            .collect::<String>(),
                    ),
                })
                .collect::<String>(),
        ),
    }
}

#[test]
fn live_pinned_control_candidates_match_complete_quotations_and_state() {
    use std::path::PathBuf;
    use std::process::Command;

    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for native control macro comparison"
        );
        eprintln!("SKIP: native control quotations require FLN_REFERENCE_LEAN");
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
    for candidate in CONTROL_CANDIDATES {
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
                Name::str(Name::anonymous(), candidate.declaration()),
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
    let dir = root.join(format!("native-control-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(
        dir.join("NativeControlMacros.lean"),
        include_str!("../../../../fln-olean/fixtures/NativeControlMacros.lean"),
    )
    .unwrap();
    let result = Command::new(&reference)
        .current_dir(&dir)
        .args(["-j1", "NativeControlMacros.lean"])
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
    let mut native = String::new();
    let mut cases = 0;
    for candidate in CONTROL_CANDIDATES {
        for context in contexts() {
            for (reference, _) in references() {
                for input in control_inputs(candidate) {
                    let execution = control_execute(
                        candidate,
                        &input,
                        &context,
                        &reference,
                        MacroLimits::default(),
                        None,
                    );
                    assert!(execution.reference_functions.is_empty());
                    assert_eq!(execution.native_functions, vec![candidate.id()]);
                    let Outcome::Complete(Ok(MacroResult::Expanded {
                        syntax,
                        state: next,
                    })) = execution.outcome
                    else {
                        panic!("{execution:?}");
                    };
                    native.push_str(&format!(
                        "ok:{}:{}\n",
                        control_syntax(&syntax),
                        next == state()
                    ));
                    cases += 1;
                }
            }
        }
        for input in [
            Syntax::Missing,
            atom(SourceInfo::None, "wrong"),
            node("User.tactic", vec![]),
        ] {
            let execution = control_execute(
                candidate,
                &input,
                &contexts()[0],
                &Syntax::Missing,
                MacroLimits::default(),
                None,
            );
            let Outcome::Complete(Ok(MacroResult::Unsupported { state: next })) = execution.outcome
            else {
                panic!("{execution:?}");
            };
            native.push_str(&format!("unsupported:{}\n", next == state()));
        }
    }
    assert_eq!(cases, 128);
    std::fs::write(dir.join("native.stdout"), &native).unwrap();
    assert_eq!(String::from_utf8(result.stdout).unwrap(), native, "{dir:?}");
    assert!(result.stderr.is_empty());
    eprintln!("native and pinned control macros: 128 exact quotations, 12 unsupported inputs");
}

const COMPOSITE_CANDIDATES: [NativeTacticMacro; 9] = [
    NativeTacticMacro::Rwa,
    NativeTacticMacro::Rw,
    NativeTacticMacro::AndThen,
    NativeTacticMacro::TrivialAssumption,
    NativeTacticMacro::TrivialRfl,
    NativeTacticMacro::TrivialContradiction,
    NativeTacticMacro::TrivialDecide,
    NativeTacticMacro::TrivialTrue,
    NativeTacticMacro::TrivialAnd,
];

fn composite_inputs(candidate: NativeTacticMacro) -> Vec<Syntax> {
    let kind = format!("Lean.Parser.Tactic.{}", candidate.input_kind());
    let wrong = || atom(SourceInfo::None, "wrong");
    let extra = || atom(SourceInfo::None, "extra");
    vec![
        node(&kind, vec![]),
        node(&kind, vec![wrong()]),
        node(&kind, vec![wrong(), control_body()]),
        node(&kind, vec![wrong(), Syntax::Missing, extra()]),
        node(&kind, vec![wrong(), control_body(), node("null", vec![])]),
        node(
            &kind,
            vec![wrong(), control_body(), node("null", vec![control_body()])],
        ),
        node(
            &kind,
            vec![
                wrong(),
                control_body(),
                node("null", vec![control_body(), Syntax::Missing]),
            ],
        ),
        node(
            &kind,
            vec![
                wrong(),
                control_body(),
                node("Other.optional", vec![control_body()]),
            ],
        ),
        node(
            &kind,
            vec![
                wrong(),
                control_body(),
                node("Lean.Parser.Tactic.rwRuleSeq", vec![]),
                node("null", vec![control_body()]),
            ],
        ),
        node(
            &kind,
            vec![
                wrong(),
                control_body(),
                node(
                    "Lean.Parser.Tactic.rwRuleSeq",
                    vec![
                        wrong(),
                        node(
                            "Other.separated",
                            vec![control_body(), atom(SourceInfo::None, ","), Syntax::Missing],
                        ),
                        control_body(),
                        extra(),
                    ],
                ),
                node("null", vec![control_body()]),
                extra(),
            ],
        ),
    ]
}

#[test]
fn native_rwa_preserves_rules_and_only_a_single_optional_location() {
    let inputs = composite_inputs(NativeTacticMacro::Rwa);
    let without = expanded_control(NativeTacticMacro::Rwa, &inputs[4]);
    for index in [2, 6, 7] {
        assert_eq!(
            expanded_control(NativeTacticMacro::Rwa, &inputs[index]),
            without,
            "a capture is optional only for a null node with exactly one child"
        );
    }
    let with = expanded_control(NativeTacticMacro::Rwa, &inputs[5]);
    for (output, count) in [(&without, 1), (&with, 2)] {
        let mut pending = vec![output];
        let mut captures = Vec::new();
        while let Some(syntax) = pending.pop() {
            if syntax.kind() == Some(&name("Client.body")) {
                captures.push(syntax);
            }
            if let Syntax::Node { args, .. } = syntax {
                pending.extend(args);
            }
        }
        assert_eq!(captures, vec![&control_body(); count]);
    }
}

#[test]
fn native_rw_nested_rule_pattern_refuses_without_losing_macro_state() {
    for input in composite_inputs(NativeTacticMacro::Rw).into_iter().take(8) {
        let execution = control_execute(
            NativeTacticMacro::Rw,
            &input,
            &contexts()[0],
            &Syntax::Missing,
            MacroLimits::default(),
            None,
        );
        assert!(matches!(
            execution.outcome,
            Outcome::Complete(Ok(MacroResult::Unsupported { state: next })) if next == state()
        ));
    }
    for input in composite_inputs(NativeTacticMacro::Rw).into_iter().skip(8) {
        expanded_control(NativeTacticMacro::Rw, &input);
    }
}

#[test]
fn live_pinned_composite_candidates_match_complete_quotations_and_state() {
    use std::path::PathBuf;
    use std::process::Command;

    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for native composite tactic comparison"
        );
        eprintln!("SKIP: native composite quotations require FLN_REFERENCE_LEAN");
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
    for candidate in COMPOSITE_CANDIDATES {
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
                Name::str(Name::anonymous(), candidate.declaration()),
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
    let dir = root.join(format!("native-composite-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(
        dir.join("NativeCompositeTacticMacros.lean"),
        include_str!("../../../../fln-olean/fixtures/NativeCompositeTacticMacros.lean"),
    )
    .unwrap();
    let result = Command::new(&reference)
        .current_dir(&dir)
        .args(["-j1", "NativeCompositeTacticMacros.lean"])
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
    let mut native = String::new();
    let mut expanded = 0;
    let mut unsupported = 0;
    for candidate in COMPOSITE_CANDIDATES {
        let mut cases = Vec::new();
        for context in contexts() {
            for (reference, _) in references() {
                for input in composite_inputs(candidate) {
                    cases.push((input, context.clone(), reference.clone()));
                }
            }
        }
        for input in [
            Syntax::Missing,
            atom(SourceInfo::None, "wrong"),
            node("User.tactic", vec![]),
        ] {
            cases.push((input, contexts()[0].clone(), Syntax::Missing));
        }
        for (input, context, reference) in cases {
            let execution = control_execute(
                candidate,
                &input,
                &context,
                &reference,
                MacroLimits::default(),
                None,
            );
            assert!(execution.reference_functions.is_empty());
            assert_eq!(execution.native_functions, vec![candidate.id()]);
            match execution.outcome {
                Outcome::Complete(Ok(MacroResult::Expanded {
                    syntax,
                    state: next,
                })) => {
                    native.push_str(&format!(
                        "ok:{}:{}\n",
                        control_syntax(&syntax),
                        next == state()
                    ));
                    expanded += 1;
                }
                Outcome::Complete(Ok(MacroResult::Unsupported { state: next })) => {
                    native.push_str(&format!("unsupported:{}\n", next == state()));
                    unsupported += 1;
                }
                other => panic!("{candidate:?}: {other:?}"),
            }
        }
    }
    assert_eq!((expanded, unsupported), (656, 91));
    std::fs::write(dir.join("native.stdout"), &native).unwrap();
    assert_eq!(String::from_utf8(result.stdout).unwrap(), native, "{dir:?}");
    assert!(result.stderr.is_empty());
    eprintln!("native and pinned composite tactics: 656 exact quotations, 91 unsupported inputs");
}

const SEQUENCING_CANDIDATES: [NativeTacticMacro; 3] = [
    NativeTacticMacro::Seq,
    NativeTacticMacro::SeqLeft,
    NativeTacticMacro::SeqRight,
];

fn sequencing_inputs(candidate: NativeTacticMacro) -> Vec<Syntax> {
    let kind = candidate.input_kind();
    let wrong = || atom(SourceInfo::None, "wrong");
    let extra = || atom(SourceInfo::None, "extra");
    let right = || {
        node(
            "Client.right",
            vec![control_body(), atom(SourceInfo::None, "right")],
        )
    };
    vec![
        node(kind, vec![]),
        node(kind, vec![wrong()]),
        node(kind, vec![control_body(), wrong()]),
        node(kind, vec![control_body(), wrong(), right()]),
        node(kind, vec![Syntax::Missing, wrong(), right(), extra()]),
        node(
            kind,
            vec![control_body(), Syntax::Missing, right(), extra()],
        ),
    ]
}

#[test]
fn native_sequencing_quotes_an_explicit_unit_thunk_with_hygienic_constants() {
    fn children<'a>(syntax: &'a Syntax, expected_kind: &str, info: SourceInfo) -> &'a [Syntax] {
        let Syntax::Node {
            info: actual,
            kind,
            args,
        } = syntax
        else {
            panic!("expected {expected_kind}, got {syntax:?}");
        };
        assert_eq!(*actual, info);
        assert_eq!(*kind, name(expected_kind));
        args
    }

    for candidate in SEQUENCING_CANDIDATES {
        let input = sequencing_inputs(candidate).swap_remove(3);
        let Syntax::Node { args: captures, .. } = &input else {
            unreachable!();
        };
        for context in contexts() {
            for (reference, expected_info) in references() {
                let execution = control_execute(
                    candidate,
                    &input,
                    &context,
                    &reference,
                    MacroLimits::default(),
                    None,
                );
                assert!(execution.reference_functions.is_empty());
                assert_eq!(execution.native_functions, vec![candidate.id()]);
                let usage = execution.vm_usage.unwrap();
                assert_eq!((usage.steps, usage.system_polls), (1, 1));
                let Outcome::Complete(Ok(MacroResult::Expanded {
                    syntax,
                    state: next,
                })) = execution.outcome
                else {
                    panic!("native {candidate:?}: {execution:?}");
                };
                assert_eq!(next, state());
                let check_identifier = |syntax: &Syntax, constant: &str| {
                    let Syntax::Ident {
                        info,
                        raw_val,
                        val,
                        preresolved,
                    } = syntax
                    else {
                        panic!("expected resolved {constant}, got {syntax:?}");
                    };
                    assert_eq!(*info, expected_info);
                    assert_eq!(raw_val.owned_backing(), Some(constant));
                    assert_eq!(raw_val.span(), span(0, constant.len()));
                    let scope_context =
                        Name::str(name(constant), "_@").append_core(&context.quotation_context);
                    assert_eq!(
                        *val,
                        Name::num(
                            Name::str(scope_context, "_hyg"),
                            context.current_macro_scope
                        )
                    );
                    let mut expected = vec![Preresolved::Decl {
                        name: name(constant),
                        fields: Vec::new(),
                    }];
                    if constant == "Unit" {
                        expected.push(Preresolved::Namespace { ns: name("Unit") });
                    }
                    assert_eq!(preresolved, &expected);
                };
                let app = children(&syntax, "Lean.Parser.Term.app", expected_info);
                assert_eq!(app.len(), 2);
                let constant = match candidate {
                    NativeTacticMacro::Seq => "Seq.seq",
                    NativeTacticMacro::SeqLeft => "SeqLeft.seqLeft",
                    NativeTacticMacro::SeqRight => "SeqRight.seqRight",
                    _ => unreachable!(),
                };
                check_identifier(&app[0], constant);
                let args = children(&app[1], "null", expected_info);
                assert_eq!(args.len(), 2);
                assert_eq!(args[0], captures[0]);
                let thunk = children(&args[1], "Lean.Parser.Term.fun", expected_info);
                assert_eq!(thunk.len(), 2);
                assert_eq!(thunk[0], atom(expected_info, "fun"));
                let body = children(&thunk[1], "Lean.Parser.Term.basicFun", expected_info);
                assert_eq!(body.len(), 4);
                let binders = children(&body[0], "null", expected_info);
                assert_eq!(binders.len(), 1);
                assert_eq!(
                    children(&binders[0], "Lean.Parser.Term.hole", expected_info),
                    &[atom(expected_info, "_")]
                );
                let annotation = children(&body[1], "null", expected_info);
                assert_eq!(annotation.len(), 1);
                let type_spec =
                    children(&annotation[0], "Lean.Parser.Term.typeSpec", expected_info);
                assert_eq!(type_spec.len(), 2);
                assert_eq!(type_spec[0], atom(expected_info, ":"));
                check_identifier(&type_spec[1], "Unit");
                assert_eq!(body[2], atom(expected_info, "=>"));
                // The right operand remains inside the thunk, including all
                // its original trivia, caller scopes, and pre-resolved data.
                assert_eq!(body[3], captures[2]);
            }
        }
    }
}

fn check_pinned_notation_candidates(
    candidates: &[NativeTacticMacro],
    inputs: fn(NativeTacticMacro) -> Vec<Syntax>,
    label: &str,
    oracle: &str,
    expected_errors: usize,
) {
    use std::path::PathBuf;
    use std::process::Command;

    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for native {label} macro comparison"
        );
        eprintln!("SKIP: native {label} quotations require FLN_REFERENCE_LEAN");
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
    for &candidate in candidates {
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
            (name("Init.Tactics"), name(candidate.declaration())),
            (
                name(candidate.module()),
                Name::str(name(candidate.declaration()), "other"),
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
        if let Some(prefix) = candidate.declaration().strip_suffix('2') {
            assert_eq!(
                NativeTacticMacro::identify(
                    &name(candidate.module()),
                    &name(&format!("{prefix}1")),
                    &partition,
                ),
                None,
                "the earlier infix registration is a different quotation"
            );
        }
    }
    // Reuse the lossless wire and capture fixtures, but execute the actual
    // pinned Init registrations rather than a restated quotation.
    let helpers = include_str!("../../../../fln-olean/fixtures/NativeControlMacros.lean")
        .strip_suffix("#eval runControlMacros\n")
        .unwrap();
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!("native-{label}-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(
        dir.join("NativeNotationMacros.lean"),
        format!("{helpers}\n{oracle}"),
    )
    .unwrap();
    let result = Command::new(&reference)
        .current_dir(&dir)
        .args(["-j1", "NativeNotationMacros.lean"])
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
    let mut native = String::new();
    let mut expanded = 0;
    let mut errors = 0;
    let mut unsupported = 0;
    let mut matching_inputs = 0;
    for &candidate in candidates {
        let mut cases = Vec::new();
        for context in contexts() {
            for (reference, _) in references() {
                for input in inputs(candidate) {
                    cases.push((input, context.clone(), reference.clone()));
                }
                cases.push((
                    atom(SourceInfo::None, candidate.input_kind()),
                    context.clone(),
                    reference.clone(),
                ));
            }
        }
        matching_inputs += cases.len();
        for input in [
            Syntax::Missing,
            atom(SourceInfo::None, "wrong"),
            node("User.term", vec![]),
            node(
                &format!("Lean.Parser.Term.{}", candidate.input_kind()),
                vec![],
            ),
        ] {
            cases.push((input, contexts()[0].clone(), Syntax::Missing));
        }
        for (input, context, reference) in cases {
            let execution = control_execute(
                candidate,
                &input,
                &context,
                &reference,
                MacroLimits::default(),
                None,
            );
            assert!(execution.reference_functions.is_empty());
            assert_eq!(execution.native_functions, vec![candidate.id()]);
            match execution.outcome {
                Outcome::Complete(Ok(MacroResult::Expanded {
                    syntax,
                    state: next,
                })) => {
                    native.push_str(&format!(
                        "ok:{}:{}\n",
                        control_syntax(&syntax),
                        next == state()
                    ));
                    expanded += 1;
                }
                Outcome::Complete(Ok(MacroResult::Unsupported { state: next })) => {
                    native.push_str(&format!("unsupported:{}\n", next == state()));
                    unsupported += 1;
                }
                Outcome::Complete(Ok(MacroResult::Error {
                    reference,
                    message,
                    state: next,
                })) => {
                    native.push_str(&format!(
                        "error:{}:{}:{}\n",
                        control_syntax(&reference),
                        control_text(&message),
                        next == state()
                    ));
                    errors += 1;
                }
                other => panic!("{candidate:?}: {other:?}"),
            }
        }
    }
    assert_eq!(
        (expanded, errors, unsupported),
        (
            matching_inputs - expected_errors,
            expected_errors,
            4 * candidates.len()
        )
    );
    std::fs::write(dir.join("native.stdout"), &native).unwrap();
    assert_eq!(String::from_utf8(result.stdout).unwrap(), native, "{dir:?}");
    assert!(result.stderr.is_empty());
    eprintln!(
        "native and pinned {label} macros: {expanded} exact quotations, {errors} diagnostic errors, {unsupported} unsupported inputs"
    );
}

#[test]
fn live_pinned_sequencing_candidates_match_complete_quotations_and_state() {
    let oracle = r#"
meta def notationCandidates : List (Macro × Name) :=
  [(«_aux_Init_Notation___macroRules_term_<*>__1», `«term_<*>_»),
   («_aux_Init_Notation___macroRules_term_<*__1», `«term_<*_»),
   («_aux_Init_Notation___macroRules_term_*>__1», `«term_*>_»)]
"#;
    check_pinned_notation_candidates(
        &SEQUENCING_CANDIDATES,
        sequencing_inputs,
        "sequencing",
        &format!("{oracle}{NOTATION_ORACLE_INPUTS}"),
        0,
    );
}

const OPERATOR_CANDIDATES: [NativeTacticMacro; 20] = [
    NativeTacticMacro::BitOr,
    NativeTacticMacro::BitXor,
    NativeTacticMacro::BitAnd,
    NativeTacticMacro::Add,
    NativeTacticMacro::Sub,
    NativeTacticMacro::Mul,
    NativeTacticMacro::Div,
    NativeTacticMacro::Mod,
    NativeTacticMacro::Pow,
    NativeTacticMacro::Append,
    NativeTacticMacro::Neg,
    NativeTacticMacro::SMul,
    NativeTacticMacro::GeAscii,
    NativeTacticMacro::LeAscii,
    NativeTacticMacro::Le,
    NativeTacticMacro::Lt,
    NativeTacticMacro::Gt,
    NativeTacticMacro::Ge,
    NativeTacticMacro::Eq,
    NativeTacticMacro::BEq,
];

fn operator_inputs(candidate: NativeTacticMacro) -> Vec<Syntax> {
    if candidate != NativeTacticMacro::Neg {
        return sequencing_inputs(candidate);
    }
    let kind = candidate.input_kind();
    let wrong = || atom(SourceInfo::None, "wrong");
    let extra = || atom(SourceInfo::None, "extra");
    vec![
        node(kind, vec![]),
        node(kind, vec![wrong()]),
        node(kind, vec![wrong(), control_body()]),
        node(
            kind,
            vec![
                Syntax::Missing,
                node(
                    "Client.right",
                    vec![control_body(), atom(SourceInfo::None, "right")],
                ),
            ],
        ),
        node(kind, vec![wrong(), control_body(), extra()]),
        node(kind, vec![extra(), Syntax::Missing, control_body()]),
    ]
}

#[test]
fn native_operator_quotes_keep_coercion_helpers_and_capture_positions() {
    for (candidate, helper) in [
        (NativeTacticMacro::Add, "binop"),
        (NativeTacticMacro::Pow, "rightact"),
        (NativeTacticMacro::SMul, "leftact"),
        (NativeTacticMacro::Neg, "unop"),
        (NativeTacticMacro::Eq, "binrel"),
        (NativeTacticMacro::BEq, "binrel_no_prop"),
    ] {
        let input = operator_inputs(candidate).swap_remove(3);
        let Syntax::Node { args: captures, .. } = &input else {
            unreachable!();
        };
        let syntax = expanded_control(candidate, &input);
        let Syntax::Node { kind, args, .. } = &syntax else {
            panic!("operator quotation is not a node: {syntax:?}");
        };
        assert_eq!(*kind, Name::str(name("Lean.Parser.Term"), helper));
        assert_eq!(args[0], atom(SourceInfo::None, &format!("{helper}%")));
        if candidate == NativeTacticMacro::Neg {
            assert_eq!(&args[2..], &[captures[1].clone()]);
        } else {
            assert_eq!(&args[2..], &[captures[0].clone(), captures[2].clone()]);
        }
        if candidate == NativeTacticMacro::Eq {
            let Syntax::Ident { preresolved, .. } = &args[1] else {
                panic!("relation quotation lost its resolved Eq: {syntax:?}");
            };
            assert_eq!(
                preresolved,
                &[
                    Preresolved::Decl {
                        name: name("Eq"),
                        fields: Vec::new()
                    },
                    Preresolved::Namespace { ns: name("Eq") },
                ]
            );
        }
    }
}

#[test]
fn live_pinned_operator_candidates_match_complete_quotations_and_state() {
    let oracle = r#"
meta def notationCandidates : List (Macro × Name) :=
  [(«_aux_Init_Notation___macroRules_term_|||__2», `«term_|||_»),
   («_aux_Init_Notation___macroRules_term_^^^__2», `«term_^^^_»),
   («_aux_Init_Notation___macroRules_term_&&&__2», `«term_&&&_»),
   («_aux_Init_Notation___macroRules_term_+__2», `«term_+_»),
   («_aux_Init_Notation___macroRules_term_-__2», `«term_-_»),
   («_aux_Init_Notation___macroRules_term_*__2», `«term_*_»),
   («_aux_Init_Notation___macroRules_term_/__2», `«term_/_»),
   («_aux_Init_Notation___macroRules_term_%__2», `«term_%_»),
   («_aux_Init_Notation___macroRules_term_^__2», `«term_^_»),
   («_aux_Init_Notation___macroRules_term_++__2», `«term_++_»),
   («_aux_Init_Notation___macroRules_term-__2», `«term-_»),
   («_aux_Init_Notation___macroRules_term_•__2», `«term_•_»),
   («_aux_Init_Notation___macroRules_term_>=__2», `«term_>=_»),
   («_aux_Init_Notation___macroRules_term_<=__2», `«term_<=_»),
   («_aux_Init_Notation___macroRules_term_≤__2», `«term_≤_»),
   («_aux_Init_Notation___macroRules_term_<__2», `«term_<_»),
   («_aux_Init_Notation___macroRules_term_>__2», `«term_>_»),
   («_aux_Init_Notation___macroRules_term_≥__2», `«term_≥_»),
   («_aux_Init_Notation___macroRules_term_=__2», `«term_=_»),
   («_aux_Init_Notation___macroRules_term_==__2», `«term_==_»)]
"#;
    check_pinned_notation_candidates(
        &OPERATOR_CANDIDATES,
        operator_inputs,
        "operators",
        &format!("{oracle}{NOTATION_ORACLE_INPUTS}"),
        0,
    );
}

const NOTATION_ORACLE_INPUTS: &str = r#"
meta def notationInputs (kind : Name) : List Syntax :=
  let wrong := Syntax.atom .none "wrong"
  let extra := Syntax.atom .none "extra"
  let right := Syntax.node .none `Client.right #[controlBody, .atom .none "right"]
  if kind == `«term-_» then
    [.node .none kind #[],
     .node .none kind #[wrong],
     .node .none kind #[wrong, controlBody],
     .node .none kind #[.missing, right],
     .node .none kind #[wrong, controlBody, extra],
     .node .none kind #[extra, .missing, controlBody]]
  else
    [.node .none kind #[],
     .node .none kind #[wrong],
     .node .none kind #[controlBody, wrong],
     .node .none kind #[controlBody, wrong, right],
     .node .none kind #[.missing, wrong, right, extra],
     .node .none kind #[controlBody, .missing, right, extra]]

meta def runNotationMacros : IO Unit := do
  let state : Macro.State := ⟨9, [(`Trace, "keep")], [`Prior]⟩
  for (macroFn, kind) in notationCandidates do
    for context in controlContexts do
      for reference in controlReferences do
        for input in notationInputs kind ++ [.atom .none (match kind with | .str _ s => s | _ => "")] do
          match macroFn input { context with ref := reference } state with
          | .ok stx next =>
            IO.println ("ok:" ++ controlSyntax stx ++ s!":{controlStateExact next}")
          | .error _ _ => IO.println "unexpected-error"
    for input in [Syntax.missing, .atom .none "wrong", .node .none `User.term #[],
      .node .none (`Lean.Parser.Term ++ kind) #[]] do
      match macroFn input ⟨default, `Client.Scope, 17, 3, 512, .missing⟩ state with
      | .error .unsupportedSyntax next =>
        IO.println s!"unsupported:{controlStateExact next}"
      | _ => IO.println "unexpected-result"

#eval runNotationMacros
"#;

const BINDER_CANDIDATES: [NativeTacticMacro; 6] = [
    NativeTacticMacro::Exists,
    NativeTacticMacro::ExistsAscii,
    NativeTacticMacro::Sigma,
    NativeTacticMacro::PSigma,
    NativeTacticMacro::DependentPair,
    NativeTacticMacro::DependentPairSort,
];

fn binder_root(candidate: NativeTacticMacro, binders: Syntax, body: Syntax) -> Syntax {
    let wrong = || atom(SourceInfo::None, "wrong");
    let extra = atom(SourceInfo::None, "extra");
    let args = if matches!(
        candidate,
        NativeTacticMacro::DependentPair | NativeTacticMacro::DependentPairSort
    ) {
        vec![binders, wrong(), body, extra]
    } else {
        vec![wrong(), binders, wrong(), body, extra]
    };
    node(candidate.input_kind(), args)
}

fn bracketed_binders(kind: &str, identifiers: Vec<Syntax>, domain: Syntax) -> Syntax {
    let wrong = || atom(SourceInfo::None, "wrong");
    node(
        kind,
        vec![wrong(), node("null", identifiers), wrong(), domain, wrong()],
    )
}

fn explicit_binders(identifiers: Vec<Syntax>, annotation: Syntax) -> Syntax {
    node(
        "Lean.explicitBinders",
        vec![node(
            "Lean.unbracketedExplicitBinders",
            vec![node("null", identifiers), annotation],
        )],
    )
}

fn binder_inputs(candidate: NativeTacticMacro) -> Vec<Syntax> {
    let named = || node("Lean.binderIdent", vec![argument(&control_body(), 0)]);
    let anonymous = || {
        node(
            "Lean.binderIdent",
            vec![Syntax::Node {
                info: SourceInfo::Synthetic {
                    pos: BytePos(1),
                    end_pos: BytePos(8),
                    canonical: true,
                },
                kind: name("Lean.Parser.Term.hole"),
                args: vec![atom(SourceInfo::None, "captured hole")],
            }],
        )
    };
    let malformed = || node("Client.binder", vec![control_body()]);
    let group = |identifiers, domain| {
        bracketed_binders("Lean.bracketedExplicitBinders", identifiers, domain)
    };
    let is_product = matches!(
        candidate,
        NativeTacticMacro::DependentPair | NativeTacticMacro::DependentPairSort
    );
    let binders = if is_product {
        vec![
            Syntax::Missing,
            group(vec![named()], control_body()),
            group(vec![named(), anonymous(), malformed()], control_body()),
            group(
                vec![anonymous(), named()],
                node("Client.domain", vec![control_body()]),
            ),
            group(Vec::new(), control_body()),
            node(
                "Lean.bracketedExplicitBinders",
                vec![Syntax::Missing, node("null", vec![named()])],
            ),
            bracketed_binders("Client.group", vec![named()], control_body()),
            group(
                vec![
                    node("Client.wrapper", vec![argument(&control_body(), 0)]),
                    malformed(),
                ],
                Syntax::Missing,
            ),
        ]
    } else {
        vec![
            Syntax::Missing,
            explicit_binders(vec![named()], node("null", Vec::new())),
            explicit_binders(
                vec![named(), anonymous(), malformed()],
                node("null", vec![atom(SourceInfo::None, ":"), control_body()]),
            ),
            node(
                "Lean.explicitBinders",
                vec![node(
                    "null",
                    vec![
                        group(vec![named(), anonymous()], control_body()),
                        group(vec![named()], node("Client.domain", vec![control_body()])),
                    ],
                )],
            ),
            explicit_binders(
                Vec::new(),
                node("null", vec![atom(SourceInfo::None, ":"), control_body()]),
            ),
            // isNone only accepts missing or an empty null node. An empty
            // node of another kind supplies a present, missing type capture.
            explicit_binders(vec![named()], node("Client.annotation", Vec::new())),
            node(
                "Lean.explicitBinders",
                vec![node("null", vec![Syntax::Missing])],
            ),
            explicit_binders(
                vec![
                    node("Client.wrapper", vec![argument(&control_body(), 0)]),
                    malformed(),
                ],
                Syntax::Missing,
            ),
        ]
    };
    let mut inputs = vec![node(candidate.input_kind(), Vec::new())];
    inputs.extend(
        binders
            .into_iter()
            .map(|binders| binder_root(candidate, binders, control_body())),
    );
    inputs
}

#[test]
fn native_binder_quotes_preserve_captures_reserved_resolution_and_diagnostics() {
    for candidate in BINDER_CANDIDATES {
        for context in contexts() {
            for (reference, info) in references() {
                let input = binder_inputs(candidate).swap_remove(3);
                let execution = control_execute(
                    candidate,
                    &input,
                    &context,
                    &reference,
                    MacroLimits::default(),
                    None,
                );
                let Outcome::Complete(Ok(MacroResult::Expanded {
                    syntax,
                    state: next,
                })) = execution.outcome
                else {
                    panic!("binder expansion failed: {execution:?}");
                };
                assert_eq!(next, state());
                let target = match candidate {
                    NativeTacticMacro::Exists | NativeTacticMacro::ExistsAscii => "Exists",
                    NativeTacticMacro::Sigma | NativeTacticMacro::DependentPair => "Sigma",
                    NativeTacticMacro::PSigma | NativeTacticMacro::DependentPairSort => "PSigma",
                    _ => unreachable!(),
                };
                let expected_value =
                    add_macro_scope(&name("_internal"), &name(target), RESERVED_MACRO_SCOPE)
                        .unwrap();
                let mut current = &syntax;
                for index in 0..3 {
                    let Syntax::Node {
                        info: actual_info,
                        kind,
                        args,
                    } = current
                    else {
                        panic!("binder fold lost its application: {current:?}");
                    };
                    assert_eq!(*actual_info, info);
                    assert_eq!(*kind, name("Lean.Parser.Term.app"));
                    assert_eq!(args.len(), 2);
                    let Syntax::Ident {
                        info: constant_info,
                        raw_val,
                        val,
                        preresolved,
                    } = &args[0]
                    else {
                        panic!("binder combinator was not an identifier");
                    };
                    assert_eq!(*constant_info, info);
                    assert_eq!(*val, expected_value);
                    assert_eq!(
                        raw_val.backing(&source()),
                        format!("{target}._@._internal._hyg.0")
                    );
                    assert_eq!(
                        *preresolved,
                        vec![Preresolved::Decl {
                            name: name(target),
                            fields: Vec::new()
                        }]
                    );
                    let lambda = argument_ref(&args[1], 0);
                    assert_eq!(lambda.kind(), Some(&name("Lean.Parser.Term.fun")));
                    let function = argument_ref(lambda, 1);
                    assert_eq!(function.kind(), Some(&name("Lean.Parser.Term.basicFun")));
                    let binder = argument_ref(argument_ref(function, 0), 0);
                    if index == 0 {
                        assert_eq!(*binder, argument(&control_body(), 0));
                    } else {
                        assert_eq!(
                            *binder,
                            Syntax::Node {
                                info,
                                kind: name("Lean.Parser.Term.hole"),
                                args: vec![atom(info, "_")],
                            }
                        );
                    }
                    let annotation = argument_ref(argument_ref(function, 1), 0);
                    assert_eq!(annotation.kind(), Some(&name("Lean.Parser.Term.typeSpec")));
                    assert_eq!(*argument_ref(annotation, 1), control_body());
                    current = argument_ref(function, 3);
                }
                assert_eq!(*current, control_body());
            }
        }
        let input = binder_inputs(candidate).swap_remove(7);
        let reference = references()[1].0.clone();
        let execution = control_execute(
            candidate,
            &input,
            &contexts()[0],
            &reference,
            MacroLimits::default(),
            None,
        );
        if matches!(
            candidate,
            NativeTacticMacro::DependentPair | NativeTacticMacro::DependentPairSort
        ) {
            assert!(matches!(
                execution.outcome,
                Outcome::Complete(Ok(MacroResult::Expanded { .. }))
            ));
        } else {
            assert!(matches!(
                execution.outcome,
                Outcome::Complete(Ok(MacroResult::Error {
                    reference: actual_reference,
                    message,
                    state: next,
                })) if actual_reference == reference
                    && message == "unexpected explicit binder"
                    && next == state()
            ));
        }
    }
}

#[test]
fn native_binder_type_duplication_obeys_output_budget_and_recovers() {
    let candidate = NativeTacticMacro::Exists;
    let input = binder_root(
        candidate,
        explicit_binders(
            vec![node("Lean.binderIdent", vec![Syntax::Missing]); 12],
            node(
                "null",
                vec![
                    atom(SourceInfo::None, ":"),
                    atom(SourceInfo::None, &"x".repeat(8192)),
                ],
            ),
        ),
        Syntax::Missing,
    );
    let limits = MacroLimits {
        syntax: SyntaxLimits {
            max_bytes: 16384,
            ..SyntaxLimits::default()
        },
        ..MacroLimits::default()
    };
    // The input fits; repeating its shared type in each generated lambda does
    // not. The native fold must stop before constructing that oversized tree.
    assert!(syntax::inject(&input, &source(), limits.syntax).is_ok());
    let limited = control_execute(
        candidate,
        &input,
        &contexts()[0],
        &Syntax::Missing,
        limits,
        None,
    );
    assert!(
        matches!(limited.outcome, Outcome::Inconclusive(_)),
        "{limited:?}"
    );
    let recovered = expanded_control(candidate, &input);
    let mut current = &recovered;
    for _ in 0..12 {
        assert_eq!(current.kind(), Some(&name("Lean.Parser.Term.app")));
        current = argument_ref(
            argument_ref(argument_ref(argument_ref(current, 1), 0), 1),
            3,
        );
    }
    assert_eq!(*current, Syntax::Missing);
}

#[test]
fn live_pinned_binder_candidates_match_complete_quotations_errors_and_state() {
    check_pinned_notation_candidates(
        &BINDER_CANDIDATES,
        binder_inputs,
        "binders",
        BINDER_ORACLE,
        32,
    );
}

const BINDER_ORACLE: &str = r#"
meta def binderCandidates : List (Macro × Name) :=
  [(«_aux_Init_NotationExtra___macroRules_term∃_,__1», `«term∃_,_»),
   («_aux_Init_NotationExtra___macroRules_termExists_,__1», `«termExists_,_»),
   («_aux_Init_NotationExtra___macroRules_termΣ_,__1», `«termΣ_,_»),
   («_aux_Init_NotationExtra___macroRules_termΣ'_,__1», `«termΣ'_,_»),
   («_aux_Init_NotationExtra___macroRules_term_×__1_1», `«term_×__1»),
   («_aux_Init_NotationExtra___macroRules_term_×'__1_1», `«term_×'__1»)]

meta def binderRoot (kind : Name) (binders body : Syntax) : Syntax :=
  let wrong := Syntax.atom .none "wrong"
  let extra := Syntax.atom .none "extra"
  if kind == `«term_×__1» || kind == `«term_×'__1» then
    .node .none kind #[binders, wrong, body, extra]
  else
    .node .none kind #[wrong, binders, wrong, body, extra]

meta def binderGroup (kind : Name) (ids : Array Syntax) (domain : Syntax) : Syntax :=
  let wrong := Syntax.atom .none "wrong"
  .node .none kind #[wrong, .node .none `null ids, wrong, domain, wrong]

meta def binderExplicit (ids : Array Syntax) (annotation : Syntax) : Syntax :=
  .node .none `Lean.explicitBinders #[.node .none `Lean.unbracketedExplicitBinders
    #[.node .none `null ids, annotation]]

meta def binderInputs (kind : Name) : List Syntax :=
  let named := Syntax.node .none `Lean.binderIdent #[controlBody[0]]
  let anonymous := Syntax.node .none `Lean.binderIdent #[
    .node (.synthetic ⟨1⟩ ⟨8⟩ true) `Lean.Parser.Term.hole #[.atom .none "captured hole"]]
  let malformed := Syntax.node .none `Client.binder #[controlBody]
  let group := binderGroup `Lean.bracketedExplicitBinders
  let binders : List Syntax :=
    if kind == `«term_×__1» || kind == `«term_×'__1» then
      [.missing,
       group #[named] controlBody,
       group #[named, anonymous, malformed] controlBody,
       group #[anonymous, named] (.node .none `Client.domain #[controlBody]),
       group #[] controlBody,
       .node .none `Lean.bracketedExplicitBinders #[.missing, .node .none `null #[named]],
       binderGroup `Client.group #[named] controlBody,
       group #[.node .none `Client.wrapper #[controlBody[0]], malformed] .missing]
    else
      [.missing,
       binderExplicit #[named] (.node .none `null #[]),
       binderExplicit #[named, anonymous, malformed] (.node .none `null #[.atom .none ":", controlBody]),
       .node .none `Lean.explicitBinders #[.node .none `null #[
         group #[named, anonymous] controlBody,
         group #[named] (.node .none `Client.domain #[controlBody])]],
       binderExplicit #[] (.node .none `null #[.atom .none ":", controlBody]),
       binderExplicit #[named] (.node .none `Client.annotation #[]),
       .node .none `Lean.explicitBinders #[.node .none `null #[.missing]],
       binderExplicit #[.node .none `Client.wrapper #[controlBody[0]], malformed] .missing]
  .node .none kind #[] :: binders.map (binderRoot kind · controlBody)

meta def runBinderMacros : IO Unit := do
  let state : Macro.State := ⟨9, [(`Trace, "keep")], [`Prior]⟩
  for (macroFn, kind) in binderCandidates do
    for context in controlContexts do
      for reference in controlReferences do
        for input in binderInputs kind ++ [.atom .none (match kind with | .str _ s => s | _ => "")] do
          match macroFn input { context with ref := reference } state with
          | .ok stx next =>
            IO.println ("ok:" ++ controlSyntax stx ++ s!":{controlStateExact next}")
          | .error (.error ref msg) next =>
            IO.println ("error:" ++ controlSyntax ref ++ ":" ++ controlText msg ++ s!":{controlStateExact next}")
          | .error .unsupportedSyntax next => IO.println s!"unsupported:{controlStateExact next}"
    for input in [Syntax.missing, .atom .none "wrong", .node .none `User.term #[],
      .node .none (`Lean.Parser.Term ++ kind) #[]] do
      match macroFn input ⟨default, `Client.Scope, 17, 3, 512, .missing⟩ state with
      | .error .unsupportedSyntax next => IO.println s!"unsupported:{controlStateExact next}"
      | _ => IO.println "unexpected-result"

#eval runBinderMacros
"#;
