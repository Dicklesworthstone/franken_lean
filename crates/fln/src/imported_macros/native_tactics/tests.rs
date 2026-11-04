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
    for candidate in CANDIDATES {
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
