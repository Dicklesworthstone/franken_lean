//! The exact pin compiles the actual `macro` declaration and independently
//! observes both choices, unsupported syntax, a diagnostic and scope state.
use super::*;
use std::path::PathBuf;
use std::process::Command;

#[test]
fn live_pinned_macro_runs_native_syntax_methods_and_matches_complete_subtrees() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from);
    let Some(reference) = reference else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for imported macro execution"
        );
        eprintln!("SKIP: imported MacroM execution requires FLN_REFERENCE_LEAN");
        return;
    };
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(
        String::from_utf8(version.stdout).unwrap().trim(),
        fln_olean::format::PIN_COMMIT
    );
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!("macro-reference-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let fixture = include_str!("../../../../fln-olean/fixtures/ir/NativeMacroModule.lean");
    std::fs::write(dir.join("NativeMacroModule.lean"), fixture).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args(["-o", "NativeMacroModule.olean", "NativeMacroModule.lean"])
        .output()
        .unwrap();
    std::fs::write(dir.join("compile.stdout"), &generated.stdout).unwrap();
    std::fs::write(dir.join("compile.stderr"), &generated.stderr).unwrap();
    assert!(
        generated.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&generated.stdout),
        String::from_utf8_lossy(&generated.stderr)
    );
    let module = crate::decode_ir_artifact(
        &std::fs::read(dir.join("NativeMacroModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    std::fs::write(dir.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .filter_map(|decl| match decl {
            IrDecl::Function { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    let choose = module
        .decls
        .iter()
        .find_map(|decl| match decl {
            IrDecl::Function { name, params, .. }
                if params.len() == 3
                    && name
                        .to_display_string()
                        .ends_with("_macroRules_userChoose_1") =>
            {
                Some(name.clone())
            }
            _ => None,
        })
        .expect("the actual macro command emitted a three-argument Macro function");
    let prepare = |entry: &Name| {
        compile(
            std::slice::from_ref(&module),
            entry,
            &VerifiedPartition::user_fixture(),
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{entry:?}: {error}; {dir:?}"))
    };
    let compiled = prepare(&choose);
    let kind = name("userChoose");
    let atom = Syntax::Atom {
        info: SourceInfo::None,
        val: "plain".into(),
    };
    let branch = Syntax::node(name("branch"), vec![leaf()]);
    let input = |first: Syntax| {
        Syntax::node(
            kind.clone(),
            vec![
                Syntax::Atom {
                    info: SourceInfo::None,
                    val: "chooseTerm%".into(),
                },
                first,
                Syntax::Atom {
                    info: SourceInfo::None,
                    val: ",".into(),
                },
                leaf(),
            ],
        )
    };
    let cases = [
        (input(atom.clone()), leaf()),
        (input(branch.clone()), branch.clone()),
    ];
    let bytecode =
        flbc::encode_canonical(compiled.callable().program(), flbc::CodecLimits::default())
            .unwrap();
    let replay = flbc::decode_canonical(&bytecode, flbc::CodecLimits::default()).unwrap();
    let entry = compiled
        .callable()
        .reference_functions()
        .iter()
        .find(|function| function.name == choose)
        .unwrap()
        .function;
    for (input, expected) in &cases {
        let report = compiled.execute(
            input,
            &source(),
            &context(),
            &MacroState::default(),
            MacroLimits::default(),
            None,
        );
        let Outcome::Complete(Ok(MacroResult::Expanded { syntax, state })) = report.outcome else {
            panic!("{report:?}; {dir:?}")
        };
        assert_eq!(syntax, *expected);
        assert_eq!(state, MacroState::default());
        let syntax = syntax::inject(input, &source(), SyntaxLimits::default()).unwrap();
        let context = make_ctor(
            layout::MACRO_CONTEXT,
            vec![
                Obj::mk_nat(0),
                inject_name(&name("Main")),
                nat(17),
                nat(0),
                nat(512),
                syntax.clone_ref(),
            ],
        );
        let state = inject_state(
            &MacroState::default(),
            &mut StateBudget::new(SyntaxLimits::default()),
        )
        .unwrap();
        let replayed = fln_vm::interpreter::execute_function(
            &replay,
            entry,
            vec![syntax, context, state],
            ExecutionLimits::default(),
            None,
        );
        let Outcome::Complete(VmExit::Returned(replayed)) = replayed else {
            panic!("{replayed:?}")
        };
        assert_eq!(
            project_result(&replayed.value, &source(), SyntaxLimits::default()).unwrap(),
            MacroResult::Expanded {
                syntax: expected.clone(),
                state: MacroState::default()
            }
        );
        for row in [
            "mirror:Lean.Name.mkStr1",
            "mirror:Lean.Syntax.isOfKind",
            "mirror:Lean.Syntax.getArg",
            "mirror:Lean.Syntax.getNumArgs",
        ] {
            assert!(
                report.native_functions.iter().any(|native| native == row),
                "missing {row}"
            );
        }
        assert!(
            report
                .reference_functions
                .iter()
                .any(|function| function.name == choose)
        );
        assert!(
            report
                .reference_functions
                .iter()
                .all(|function| function.producer() == "reference"
                    && !function.name.to_display_string().starts_with("Lean."))
        );
    }
    let unsupported = compiled.execute(
        &leaf(),
        &source(),
        &context(),
        &MacroState::default(),
        MacroLimits::default(),
        None,
    );
    assert!(
        matches!(unsupported.outcome, Outcome::Complete(Ok(MacroResult::Unsupported { state })) if state == MacroState::default())
    );
    let scoped = prepare(&name("scopedMacro")).execute(
        &leaf(),
        &source(),
        &context(),
        &MacroState::default(),
        MacroLimits::default(),
        None,
    );
    assert!(
        matches!(scoped.outcome, Outcome::Complete(Ok(MacroResult::Expanded { syntax, state })) if syntax == leaf() && state.macro_scope == 1)
    );
    let diagnostic = prepare(&name("errorMacro")).execute(
        &leaf(),
        &source(),
        &context(),
        &MacroState::default(),
        MacroLimits::default(),
        None,
    );
    assert!(
        matches!(diagnostic.outcome, Outcome::Complete(Ok(MacroResult::Error { reference, message, state })) if reference == leaf() && message == "λ\0error" && state == MacroState::default())
    );
    let namespace = prepare(&name("namespaceMacro")).execute(
        &leaf(),
        &source(),
        &context(),
        &MacroState::default(),
        MacroLimits::default(),
        None,
    );
    assert!(matches!(
        namespace.outcome,
        Outcome::Complete(Err(MacroExecutionError::Runtime(
            VmRefusal::MacroLookupUnavailable {
                operation: "Lean.Macro.getCurrNamespace"
            }
        )))
    ));

    let context_entry = module
        .decls
        .iter()
        .find_map(|declaration| match declaration {
            IrDecl::Function { name, .. }
                if name
                    .to_display_string()
                    .ends_with("_macroRules_contextChoose_1") =>
            {
                Some(name.clone())
            }
            _ => None,
        })
        .expect("the actual context macro has an entry");
    let context_macro = prepare(&context_entry);
    let context_input = Syntax::node(
        name("contextChoose"),
        vec![
            Syntax::atom(SourceInfo::None, "contextTerm%"),
            branch.clone(),
            Syntax::atom(SourceInfo::None, ","),
            leaf(),
        ],
    );
    for (scope, expected) in [(17, branch.clone()), (18, leaf()), (17, branch.clone())] {
        let current = MacroContext {
            current_macro_scope: scope,
            ..context()
        };
        let report = context_macro.execute(
            &context_input,
            &source(),
            &current,
            &MacroState::default(),
            MacroLimits::default(),
            None,
        );
        assert!(
            matches!(report.outcome, Outcome::Complete(Ok(MacroResult::Expanded { syntax, state }))
            if syntax == expected && state == MacroState::default()),
            "scope {scope}"
        );
    }
    let fields_macro = prepare(&name("contextFields"));
    for (quotation, depth, maximum) in [("Main", 0, 512), ("Other", 3, 512), ("Main", 512, 512)] {
        let current = MacroContext {
            quotation_context: name(quotation),
            current_recursion_depth: depth,
            max_recursion_depth: maximum,
            ..context()
        };
        let expected = if depth == maximum {
            leaf()
        } else {
            Syntax::node(name(quotation), vec![leaf(), leaf()])
        };
        let report = fields_macro.execute(
            &leaf(),
            &source(),
            &current,
            &MacroState::default(),
            MacroLimits::default(),
            None,
        );
        assert!(
            matches!(report.outcome, Outcome::Complete(Ok(MacroResult::Expanded { syntax, state }))
            if syntax == expected && state == MacroState::default()),
            "{quotation}, {depth}/{maximum}"
        );
    }
    let inspect = prepare(&name("inspectSyntaxMacro"));
    let identify = prepare(&name("idSyntaxMacro"));
    let rename = prepare(&name("replaceSyntaxKindMacro"));
    let mut native_rows = BTreeSet::new();
    let original_node = Syntax::Node {
        info: SourceInfo::Synthetic {
            pos: BytePos(1),
            end_pos: BytePos(3),
            canonical: true,
        },
        kind: name("branch"),
        args: vec![leaf()],
    };
    for (input, expected_kind, expected_id, children, missing, ident) in [
        (
            Syntax::Missing,
            name("missing"),
            Name::anonymous(),
            vec![],
            true,
            false,
        ),
        (
            leaf(),
            name("ident"),
            Name::num(name("Main._hyg"), 17),
            vec![],
            false,
            true,
        ),
        (
            Syntax::atom(SourceInfo::None, "A.B\0🙂"),
            Name::str(Name::anonymous(), "A.B\0🙂"),
            Name::anonymous(),
            vec![],
            false,
            false,
        ),
        (
            original_node.clone(),
            name("branch"),
            Name::anonymous(),
            vec![leaf()],
            false,
            false,
        ),
        (
            Syntax::atom(SourceInfo::None, "ident"),
            name("ident"),
            Name::anonymous(),
            vec![],
            false,
            false,
        ),
    ] {
        let expected_inspection = if ident {
            Syntax::node(expected_id.clone(), vec![input.clone()])
        } else {
            Syntax::node(expected_kind, children.clone())
        };
        let expected_replacement = match &input {
            Syntax::Node { info, args, .. } => Syntax::Node {
                info: *info,
                kind: name("renamed"),
                args: args.clone(),
            },
            _ => input.clone(),
        };
        for (compiled, expected) in [
            (&inspect, expected_inspection),
            (&identify, Syntax::node(expected_id, children)),
            (&rename, expected_replacement),
        ] {
            let report = compiled.execute(
                &input,
                &source(),
                &context(),
                &MacroState::default(),
                MacroLimits::default(),
                None,
            );
            native_rows.extend(report.native_functions);
            assert!(
                report
                    .reference_functions
                    .iter()
                    .all(|function| !function.name.to_display_string().starts_with("Lean.")),
                "toolchain implementation must not execute as imported IR"
            );
            assert!(
                matches!(report.outcome,
                    Outcome::Complete(Ok(MacroResult::Expanded { syntax, state }))
                    if syntax == expected && state == MacroState::default()),
                "inspection/rewrite of {input:?} (missing={missing}, ident={ident})"
            );
        }
    }
    for row in [
        "mirror:Lean.Syntax.getKind",
        "mirror:Lean.Syntax.setKind",
        "mirror:Lean.Syntax.getArgs",
        "mirror:Lean.Syntax.isMissing",
        "mirror:Lean.Syntax.isIdent",
        "mirror:Lean.Syntax.getId",
    ] {
        assert!(
            native_rows.contains(row),
            "the real macro did not select {row}"
        );
    }

    let positions = prepare(&name("syntaxPositionsMacro"));
    let canonical_positions = prepare(&name("canonicalSyntaxPositionsMacro"));
    let info_positions = prepare(&name("infoPositionsMacro"));
    let canonical_info_positions = prepare(&name("canonicalInfoPositionsMacro"));
    let noncanonical = SourceInfo::Synthetic {
        pos: BytePos(0),
        end_pos: BytePos(4),
        canonical: false,
    };
    let no_info = Syntax::atom(SourceInfo::None, "none");
    let filtered_node = Syntax::Node {
        info: noncanonical,
        kind: name("outer"),
        args: vec![leaf()],
    };
    let position_output = |start: Option<usize>, end: Option<usize>| {
        let atom = |position: Option<usize>, label| {
            position.map_or(Syntax::Missing, |position| {
                Syntax::atom(
                    SourceInfo::Synthetic {
                        pos: BytePos(position),
                        end_pos: BytePos(position),
                        canonical: true,
                    },
                    label,
                )
            })
        };
        Syntax::node(
            name("positions"),
            vec![atom(start, "start"), atom(end, "end")],
        )
    };
    let state = MacroState {
        macro_scope: 23,
        trace_messages: vec![(name("Positions"), "preserved".into())],
        expanded_macro_declarations: vec![name("Earlier.macro")],
    };
    for (input, all, canonical, info, canonical_info) in [
        (
            leaf(),
            (Some(1), Some(3)),
            (Some(1), Some(3)),
            (Some(1), Some(3)),
            (Some(1), Some(3)),
        ),
        (
            Syntax::Missing,
            (None, None),
            (None, None),
            (None, None),
            (None, None),
        ),
        (
            Syntax::atom(noncanonical, "synthetic"),
            (Some(0), Some(4)),
            (None, None),
            (Some(0), Some(4)),
            (None, None),
        ),
        (
            Syntax::node(
                name("outer"),
                vec![Syntax::Missing, leaf(), no_info.clone()],
            ),
            (Some(1), Some(3)),
            (Some(1), Some(3)),
            (Some(1), Some(3)),
            (Some(1), Some(3)),
        ),
        (
            Syntax::node(name("outer"), vec![no_info, leaf()]),
            (None, Some(3)),
            (None, Some(3)),
            (None, None),
            (None, None),
        ),
        (
            filtered_node,
            (Some(0), Some(4)),
            (None, Some(3)),
            (Some(0), Some(4)),
            (None, None),
        ),
    ] {
        for (compiled, (start, end)) in [
            (&positions, all),
            (&canonical_positions, canonical),
            (&info_positions, info),
            (&canonical_info_positions, canonical_info),
        ] {
            let report = compiled.execute(
                &input,
                &source(),
                &context(),
                &state,
                MacroLimits::default(),
                None,
            );
            native_rows.extend(report.native_functions);
            assert!(
                report.reference_functions.iter().all(|function| {
                    function.producer() == "reference"
                        && !function.name.to_display_string().starts_with("Lean.")
                }),
                "toolchain position methods must run natively"
            );
            let Outcome::Complete(Ok(MacroResult::Expanded {
                syntax,
                state: next,
            })) = report.outcome
            else {
                panic!(
                    "source positions did not complete for {input:?}: {:?}",
                    report.outcome
                );
            };
            assert_eq!(
                syntax,
                position_output(start, end),
                "source positions for {input:?}"
            );
            assert_eq!(
                next, state,
                "position inspection preserves all MacroM state"
            );
        }
    }
    for row in [
        "mirror:Lean.SourceInfo.getPos?",
        "mirror:Lean.SourceInfo.getTailPos?",
        "mirror:Lean.Syntax.getPos?",
        "mirror:Lean.Syntax.getTailPos?",
    ] {
        assert!(
            native_rows.contains(row),
            "actual imported MacroM did not select {row}"
        );
    }

    let reference_info = prepare(&name("referenceInfoMacro"));
    let canonical_reference_info = prepare(&name("canonicalReferenceInfoMacro"));
    let atom_from = prepare(&name("atomFromMacro"));
    let canonical_atom_from = prepare(&name("canonicalAtomFromMacro"));
    let plain_atom = prepare(&name("atomMacro"));
    for (input, ordinary, preferred) in [
        (leaf(), Some((1, 3, false)), Some((1, 3, true))),
        (Syntax::Missing, None, None),
        (Syntax::atom(SourceInfo::None, "none"), None, None),
        (
            Syntax::atom(noncanonical, "synthetic"),
            Some((0, 4, false)),
            Some((0, 4, false)),
        ),
        (
            Syntax::Node {
                info: noncanonical,
                kind: name("outer"),
                args: vec![leaf()],
            },
            Some((0, 4, false)),
            Some((0, 4, false)),
        ),
        (
            Syntax::node(
                name("outer"),
                vec![Syntax::atom(SourceInfo::None, "no head"), leaf()],
            ),
            None,
            None,
        ),
        (
            Syntax::node(
                name("outer"),
                vec![leaf(), Syntax::atom(noncanonical, "last")],
            ),
            Some((1, 4, false)),
            Some((1, 3, true)),
        ),
        (
            Syntax::node(
                name("outer"),
                vec![Syntax::atom(noncanonical, "first"), leaf()],
            ),
            Some((0, 3, false)),
            Some((0, 3, false)),
        ),
    ] {
        for (compiled, expected) in [
            (&reference_info, ordinary),
            (&canonical_reference_info, preferred),
            (&atom_from, ordinary),
            (&canonical_atom_from, preferred),
        ] {
            let report = compiled.execute(
                &input,
                &source(),
                &context(),
                &state,
                MacroLimits::default(),
                None,
            );
            native_rows.extend(report.native_functions);
            assert!(
                report.reference_functions.iter().all(|function| {
                    function.producer() == "reference"
                        && !function.name.to_display_string().starts_with("Lean.")
                }),
                "source constructors must run natively"
            );
            let Outcome::Complete(Ok(MacroResult::Expanded {
                syntax,
                state: next,
            })) = report.outcome
            else {
                panic!(
                    "source construction did not complete for {input:?}: {:?}",
                    report.outcome
                );
            };
            let info = expected.map_or(SourceInfo::None, |(start, stop, canonical)| {
                SourceInfo::Synthetic {
                    pos: BytePos(start),
                    end_pos: BytePos(stop),
                    canonical,
                }
            });
            assert_eq!(
                syntax,
                Syntax::atom(info, "reference\0λ"),
                "source construction for {input:?}"
            );
            assert_eq!(
                next, state,
                "source construction preserves every MacroM state field"
            );
        }
    }
    for (input, expected) in [
        (leaf(), ""),
        (Syntax::atom(noncanonical, "λ\0🙂"), "λ\0🙂"),
        (Syntax::Missing, ""),
    ] {
        let report = plain_atom.execute(
            &input,
            &source(),
            &context(),
            &state,
            MacroLimits::default(),
            None,
        );
        native_rows.extend(report.native_functions);
        assert!(report.reference_functions.iter().all(|function| {
            function.producer() == "reference"
                && !function.name.to_display_string().starts_with("Lean.")
        }));
        assert!(
            matches!(report.outcome, Outcome::Complete(Ok(MacroResult::Expanded { syntax, state: next }))
            if syntax == Syntax::atom(SourceInfo::None, expected) && next == state)
        );
    }
    for row in [
        "mirror:Lean.SourceInfo.fromRef",
        "mirror:Lean.mkAtomFrom",
        "mirror:Lean.mkAtom",
    ] {
        assert!(
            native_rows.contains(row),
            "actual imported MacroM did not select {row}"
        );
    }

    let scoped_ref = prepare(&name("referenceScopeMacro"));
    let public_error = prepare(&name("publicErrorMacro"));
    let located_error = prepare(&name("publicErrorAtMacro"));
    let public_unsupported = prepare(&name("publicUnsupportedMacro"));
    let old_ref = leaf();
    let positioned = Syntax::atom(
        SourceInfo::Synthetic {
            pos: BytePos(0),
            end_pos: BytePos(4),
            canonical: false,
        },
        "positioned",
    );
    let no_head = Syntax::node(
        name("headNone"),
        vec![Syntax::atom(SourceInfo::None, "none"), leaf()],
    );
    let invoke_with_ref = |compiled: &CompiledMacro, input: &Syntax| {
        let report = compiled.execute_with_methods(
            input,
            MacroInvocation {
                source: &source(),
                context: &context(),
                state: &state,
                lookup: None,
            },
            MacroLimits::default(),
            None,
            None,
            Some(&old_ref),
        );
        assert!(report.reference_functions.iter().all(|function| {
            function.producer() == "reference"
                && !function.name.to_display_string().starts_with("Lean.")
        }));
        report
    };
    for (input, selected) in [
        (Syntax::Missing, old_ref.clone()),
        (Syntax::node(name("empty"), vec![]), old_ref.clone()),
        (no_head, old_ref.clone()),
        (positioned.clone(), positioned.clone()),
        (old_ref.clone(), old_ref.clone()),
        (
            Syntax::node(name("skipped"), vec![Syntax::Missing, positioned.clone()]),
            Syntax::node(name("skipped"), vec![Syntax::Missing, positioned]),
        ),
    ] {
        let report = invoke_with_ref(&scoped_ref, &input);
        native_rows.extend(report.native_functions);
        assert_eq!(
            completed_macro_result(report.outcome),
            MacroResult::Expanded {
                syntax: Syntax::node(
                    name("refs"),
                    vec![old_ref.clone(), selected.clone(), old_ref.clone()]
                ),
                state: state.clone(),
            }
        );
        let report = invoke_with_ref(&located_error, &input);
        native_rows.extend(report.native_functions);
        assert_eq!(
            completed_macro_result(report.outcome),
            MacroResult::Error {
                reference: selected,
                message: "public\0λ".into(),
                state: state.clone(),
            }
        );
    }
    for (compiled, row, missing) in [
        (
            &public_error,
            "mirror:Lean.Macro.throwError._redArg",
            MacroResult::Error {
                reference: old_ref.clone(),
                message: "public\0λ".into(),
                state: state.clone(),
            },
        ),
        (
            &public_unsupported,
            "mirror:Lean.Macro.throwUnsupported._redArg",
            MacroResult::Unsupported {
                state: state.clone(),
            },
        ),
    ] {
        // The retained error branch is present in the imported IR closure even
        // when the actual invocation takes the successful branch.
        let success = invoke_with_ref(compiled, &old_ref);
        assert!(success.native_functions.iter().any(|native| native == row));
        assert_eq!(
            completed_macro_result(success.outcome),
            MacroResult::Expanded {
                syntax: old_ref.clone(),
                state: state.clone()
            }
        );
        let failure = invoke_with_ref(compiled, &Syntax::Missing);
        native_rows.extend(failure.native_functions);
        assert_eq!(completed_macro_result(failure.outcome), missing);
    }
    for row in [
        "mirror:Lean.replaceRef",
        "mirror:Lean.Macro.throwError._redArg",
        "mirror:Lean.Macro.throwErrorAt._redArg",
        "mirror:Lean.Macro.throwUnsupported._redArg",
    ] {
        assert!(
            native_rows.contains(row),
            "actual user MacroM did not select {row}"
        );
    }
    check_public_error_dispatch(&dir, &module, &users, &state);

    let mut exhausted = MacroLimits::default();
    exhausted.vm.max_steps = 0;
    assert!(matches!(
        fields_macro
            .execute(
                &leaf(),
                &source(),
                &context(),
                &MacroState::default(),
                exhausted,
                None
            )
            .outcome,
        Outcome::Inconclusive(_)
    ));
    assert!(matches!(
        fields_macro
            .execute(
                &leaf(),
                &source(),
                &context(),
                &MacroState::default(),
                MacroLimits::default(),
                Some(&|| true)
            )
            .outcome,
        Outcome::Inconclusive(_)
    ));
    assert!(matches!(
        fields_macro
            .execute(
                &leaf(),
                &source(),
                &context(),
                &MacroState::default(),
                MacroLimits::default(),
                None
            )
            .outcome,
        Outcome::Complete(Ok(MacroResult::Expanded { .. }))
    ));

    let attach = prepare(&name("attachScopeMacro"));
    let fresh = prepare(&name("freshIdentifierMacro"));
    let mut plain = leaf();
    let Syntax::Ident { val, .. } = &mut plain else {
        panic!("identifier fixture");
    };
    *val = name("α");
    let initial_state = MacroState {
        macro_scope: 10,
        trace_messages: vec![(name("Trace"), "opaque\0λ".into())],
        expanded_macro_declarations: vec![name("Previous.macro")],
    };
    let scoped_name = |scope| Name::num(name("α._@.Main._hyg"), scope);
    let run_scope = |compiled: &CompiledMacro,
                     input: &Syntax,
                     context: &MacroContext,
                     state: &MacroState,
                     expected_name: Name,
                     expected_counter| {
        let report = compiled.execute(
            input,
            &source(),
            context,
            state,
            MacroLimits::default(),
            None,
        );
        assert!(
            report
                .native_functions
                .iter()
                .any(|row| row == "mirror:Lean.Macro.addMacroScope"),
            "the actual MacroM must select its native scope row: {report:?}"
        );
        assert!(report.reference_functions.iter().all(|function| {
            function.producer() == "reference"
                && !function.name.to_display_string().starts_with("Lean.")
        }));
        let mut expected = input.clone();
        let Syntax::Ident { val, .. } = &mut expected else {
            panic!("scope input must be an identifier");
        };
        *val = expected_name;
        let mut expected_state = state.clone();
        expected_state.macro_scope = expected_counter;
        let Outcome::Complete(Ok(MacroResult::Expanded { syntax, state })) = report.outcome else {
            panic!("scope attachment did not complete");
        };
        assert_eq!(
            syntax, expected,
            "complete source/name/preresolution payload"
        );
        assert_eq!(state, expected_state, "complete caller state");
        (syntax, state)
    };
    run_scope(
        &attach,
        &plain,
        &context(),
        &initial_state,
        scoped_name(17),
        10,
    );
    let (first, first_state) = run_scope(
        &fresh,
        &plain,
        &context(),
        &initial_state,
        scoped_name(10),
        11,
    );
    let (second, second_state) = run_scope(
        &fresh,
        &first,
        &context(),
        &first_state,
        Name::num(scoped_name(10), 11),
        12,
    );
    let other_context = MacroContext {
        quotation_context: name("Other.Module"),
        current_macro_scope: 99,
        ..context()
    };
    let imported = Name::num(Name::num(name("α._@.Main"), 10), 11);
    let changed_name = Name::num(
        Name::str(imported.append_core(&name("Other.Module")), "_hyg"),
        99,
    );
    run_scope(
        &attach,
        &second,
        &other_context,
        &second_state,
        changed_name,
        12,
    );

    let oracle_entry = choose
        .to_display_string()
        .replace("NativeMacroModule", "Oracle");
    let oracle_source = format!(
        "{fixture}\n{}",
        ORACLE.replace("MACRO_ENTRY", &oracle_entry).replace(
            "CONTEXT_ENTRY",
            &context_entry
                .to_display_string()
                .replace("NativeMacroModule", "Oracle")
        )
    );
    std::fs::write(dir.join("Oracle.lean"), oracle_source).unwrap();
    let oracle = Command::new(&reference)
        .current_dir(&dir)
        .arg("Oracle.lean")
        .output()
        .unwrap();
    std::fs::write(dir.join("oracle.stdout"), &oracle.stdout).unwrap();
    std::fs::write(dir.join("oracle.stderr"), &oracle.stderr).unwrap();
    assert!(
        oracle.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&oracle.stdout),
        String::from_utf8_lossy(&oracle.stderr)
    );
    assert_eq!(
        oracle.stdout,
        b"[true, true, true, true, true, true, true, true, true, true]\n[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]\n[true, true, true, true, true]\n[true, true, true, true, true, true]\n[true, true, true, true, true, true, true, true, true]\n[true, true, true, true, true, true, true, true, true]\n"
    );
    assert!(oracle.stderr.is_empty());

    // A real executable wrong-expansion control: change getArg's selected
    // argument index in the imported macro while preserving its valid IR.
    // The result still executes but fails equality against the pin's subtree.
    let mut mutant = module.clone();
    let mut changed = false;
    for declaration in &mut mutant.decls {
        if let IrDecl::Function { name, body, .. } = declaration
            && name.to_display_string() == format!("{}._redArg", choose.to_display_string())
        {
            fn alter(body: &mut IrBody, changed: &mut bool) {
                for stmt in &mut body.stmts {
                    if let IrStmt::VDecl {
                        expr: IrExpr::Lit(IrLit::Num(IrNat::Small(index))),
                        ..
                    } = stmt
                        && *index == 3
                    {
                        *index = 0;
                        *changed = true;
                    }
                    if let IrStmt::JDecl { value, .. } = stmt {
                        alter(value, changed);
                    }
                }
                if let IrTerminal::Case { alts, .. } = body.terminal.as_mut() {
                    for alt in alts {
                        match alt {
                            fln_olean::ir::IrAlt::Ctor { body, .. }
                            | fln_olean::ir::IrAlt::Default { body } => alter(body, changed),
                        }
                    }
                }
            }
            alter(body, &mut changed);
        }
    }
    assert!(
        changed,
        "negative control must reach the actual macro's getArg index"
    );
    let mutant = compile(
        &[mutant],
        &choose,
        &VerifiedPartition::user_fixture(),
        &users,
        IrExecutionLimits::default(),
    )
    .unwrap();
    let wrong = mutant.execute(
        &cases[0].0,
        &source(),
        &context(),
        &MacroState::default(),
        MacroLimits::default(),
        None,
    );
    let Outcome::Complete(Ok(MacroResult::Expanded { syntax: wrong, .. })) = wrong.outcome else {
        panic!("{wrong:?}")
    };
    assert_ne!(wrong, cases[0].1);
}

fn completed_macro_result(
    outcome: Outcome<Result<MacroResult, MacroExecutionError>>,
) -> MacroResult {
    match outcome {
        Outcome::Complete(Ok(result)) => result,
        other => panic!("native MacroM invocation did not complete: {other:?}"),
    }
}

fn check_public_error_dispatch(
    dir: &std::path::Path,
    module: &IrModule,
    users: &BTreeSet<Name>,
    state: &MacroState,
) {
    use crate::imported_macros::registrations::{
        MacroDispatchLimits, MacroRegistrationModule, MacroRegistryLimits, RegisteredExpansion,
        RegisteredMacros,
    };
    use fln_olean::region::{OleanView, WalkBudget};

    let public = std::fs::read(dir.join("NativeMacroModule.olean")).unwrap();
    let server = std::fs::read(dir.join("NativeMacroModule.olean.server")).unwrap();
    let private = std::fs::read(dir.join("NativeMacroModule.olean.private")).unwrap();
    let decoded = crate::decode_olean_module_artifacts(
        &public,
        &server,
        &private,
        crate::OleanDecodeLimits::new(public.len() + server.len() + private.len()),
    )
    .unwrap();
    let extensions = OleanView::parse_with_dependencies(&private, &[&public, &server])
        .unwrap()
        .extension_payloads(WalkBudget::default(), 32 * 1024 * 1024)
        .unwrap();
    // Test the decoded-owner caller boundary with actual pinned journals and
    // IR. This does not claim admission of Init or synthesize a census gate.
    let root = crate::Environment::new().logical_root(&crate::KVMap::new());
    let checked = crate::CheckedOleanModule {
        name: name("NativeMacroModule"),
        decoded,
        base_logical_root: root,
        result_logical_root: root,
        declarations: Vec::new(),
    };
    let admitted = checked
        .decoded
        .constants
        .iter()
        .fold(crate::Environment::new(), |environment, declaration| {
            environment.add_decl(declaration.clone()).unwrap()
        });
    let registry = RegisteredMacros::prepare(
        &[MacroRegistrationModule {
            checked: &checked,
            extensions: &extensions,
        }],
        &admitted,
        std::slice::from_ref(module),
        &VerifiedPartition::user_fixture(),
        users,
        MacroRegistryLimits::default(),
    )
    .unwrap();
    assert_eq!(
        registry
            .declarations(&name("referenceChoice"))
            .cloned()
            .collect::<Vec<_>>(),
        [name("referenceGuard"), name("referenceFallback")]
    );
    let input = |candidate| {
        Syntax::node(
            name("referenceChoice"),
            vec![
                Syntax::atom(SourceInfo::None, "referenceChoice%"),
                candidate,
            ],
        )
    };
    let dispatch = |input: &Syntax| {
        registry.expand_root(
            input,
            &source(),
            &context(),
            state.clone(),
            MacroDispatchLimits::default(),
            None,
        )
    };
    let fallthrough = dispatch(&input(Syntax::Missing));
    let mut expected_state = state.clone();
    expected_state.macro_scope += 3;
    expected_state
        .expanded_macro_declarations
        .insert(0, name("referenceFallback"));
    let expected = Syntax::node(
        fln_syntax::hygiene::add_macro_scope(
            &name("Main"),
            &name("fallback"),
            state.macro_scope + 2,
        )
        .unwrap(),
        vec![],
    );
    assert!(
        matches!(&fallthrough.outcome, Outcome::Complete(Ok(RegisteredExpansion::Expanded { declaration, syntax, state, .. }))
        if declaration == &name("referenceFallback") && syntax == &expected && state == &expected_state),
        "{fallthrough:?}"
    );
    assert_eq!(fallthrough.attempts.len(), 2);
    assert!(
        fallthrough.attempts[0]
            .native_functions
            .iter()
            .any(|row| row == "mirror:Lean.Macro.throwUnsupported._redArg")
    );
    let unsupported = dispatch(&Syntax::node(name("referenceChoice"), vec![]));
    expected_state.expanded_macro_declarations = state.expanded_macro_declarations.clone();
    assert!(
        matches!(&unsupported.outcome, Outcome::Complete(Ok(RegisteredExpansion::Unsupported { state })) if state == &expected_state),
        "{unsupported:?}"
    );
    assert_eq!(unsupported.attempts.len(), 2);

    let mut noncanonical = leaf();
    if let Syntax::Ident { info, .. } = &mut noncanonical {
        *info = SourceInfo::Synthetic {
            pos: BytePos(0),
            end_pos: BytePos(4),
            canonical: false,
        };
    }
    let no_head = Syntax::node(
        name("headNone"),
        vec![Syntax::atom(SourceInfo::None, "no head"), leaf()],
    );
    let skipped = Syntax::node(name("skipped"), vec![Syntax::Missing, leaf()]);
    expected_state.macro_scope = state.macro_scope + 2;
    for (candidate, own_ref) in [
        (leaf(), true),
        (noncanonical, true),
        (no_head, false),
        (skipped, true),
    ] {
        let input = input(candidate.clone());
        let reference = if own_ref { candidate } else { input.clone() };
        let report = dispatch(&input);
        assert!(
            matches!(&report.outcome, Outcome::Complete(Ok(RegisteredExpansion::Error { declaration, reference: actual, message, state, .. }))
            if declaration == &name("referenceGuard") && actual == &reference && message == "located\0λ" && state == &expected_state),
            "{report:?}"
        );
        assert_eq!(
            report.attempts.len(),
            1,
            "a located diagnostic must terminate this candidate chain"
        );
        assert!(
            report.attempts[0]
                .native_functions
                .iter()
                .any(|row| row == "mirror:Lean.Macro.throwErrorAt._redArg")
        );
    }
    let nested = Syntax::node(
        name("referenceOuter"),
        vec![
            Syntax::atom(SourceInfo::None, "referenceOuter%"),
            input(Syntax::atom(SourceInfo::None, "plain")),
        ],
    );
    let report = dispatch(&nested);
    expected_state.macro_scope = state.macro_scope + 3;
    assert!(
        matches!(&report.outcome, Outcome::Complete(Ok(RegisteredExpansion::Error { reference, message, state, .. }))
        if reference == &nested && message == "outer\0λ" && state == &expected_state),
        "{report:?}"
    );
    assert_eq!(report.attempts.len(), 2);
    assert!(
        report.attempts[1]
            .native_functions
            .iter()
            .any(|row| row == "mirror:Lean.Macro.throwError._redArg")
    );
    for attempt in &report.attempts {
        assert!(
            attempt
                .reference_functions
                .iter()
                .all(|function| !function.name.to_display_string().starts_with("Lean."))
        );
    }
    let mut limited = MacroDispatchLimits::default();
    limited.execution.vm.max_steps = 0;
    for (limits, cancel) in [(limited, false), (MacroDispatchLimits::default(), true)] {
        let stopped = registry.expand_root(
            &input(Syntax::Missing),
            &source(),
            &context(),
            state.clone(),
            limits,
            Some(&|| cancel),
        );
        assert!(matches!(stopped.outcome, Outcome::Inconclusive(_)));
        assert!(
            stopped.attempts.len() <= 1,
            "a VM stop must not select the fallback"
        );
    }
    assert!(matches!(
        dispatch(&input(Syntax::Missing)).outcome,
        Outcome::Complete(Ok(RegisteredExpansion::Expanded { .. }))
    ));
}

// The oracle checks every field of the sensitive returned identifier, including
// raw backing, byte positions, hygiene name and pre-resolution. No pretty-printer
// or Syntax equality that could ignore source information supplies the verdict.
const ORACLE: &str = r#"
def sampleSource : String := " α "
def sampleLeaf : Lean.Syntax :=
  .ident (.original ⟨sampleSource, ⟨0⟩, ⟨1⟩⟩ ⟨1⟩ ⟨sampleSource, ⟨3⟩, ⟨4⟩⟩ ⟨3⟩)
    ⟨sampleSource, ⟨1⟩, ⟨3⟩⟩ (Lean.Name.num `Main._hyg 17)
    [.namespace `N, .decl `N.x ["field"]]
def leafExact : Lean.Syntax → Bool
  | .ident (.original leading pos trailing stop) raw val [.namespace ns, .decl decl [field]] =>
    leading.str == sampleSource && leading.startPos.byteIdx == 0 && leading.stopPos.byteIdx == 1 &&
    pos.byteIdx == 1 && trailing.str == sampleSource && trailing.startPos.byteIdx == 3 &&
    trailing.stopPos.byteIdx == 4 && stop.byteIdx == 3 && raw.str == sampleSource &&
    raw.startPos.byteIdx == 1 && raw.stopPos.byteIdx == 3 && val == Lean.Name.num `Main._hyg 17 &&
    ns == `N && decl == `N.x && field == "field"
  | _ => false
def branchExact : Lean.Syntax → Bool
  | .node .none kind args => kind == `branch && args.size == 1 && leafExact args[0]!
  | _ => false
def sampleInput (first : Lean.Syntax) : Lean.Syntax :=
  .node .none `userChoose #[.atom .none "chooseTerm%", first, .atom .none ",", sampleLeaf]
def sampleContext : Lean.Macro.Context :=
  ⟨default, `Main, 17, 0, 512, sampleLeaf⟩
def contextInput : Lean.Syntax :=
  .node .none `contextChoose #[.atom .none "contextTerm%", .node .none `branch #[sampleLeaf], .atom .none ",", sampleLeaf]
def contextNodeExact (expected : Lean.Name) : Lean.Syntax → Bool
  | .node .none kind args => kind == expected && args.size == 2 && leafExact args[0]! && leafExact args[1]!
  | _ => false
#eval show List Bool from
  let first := match MACRO_ENTRY (sampleInput (.atom .none "plain")) sampleContext default with
    | .ok out state => leafExact out && state.macroScope == 0 && state.traceMsgs.isEmpty
    | _ => false
  let second := match MACRO_ENTRY (sampleInput (.node .none `branch #[sampleLeaf])) sampleContext default with
    | .ok out state => branchExact out && state.macroScope == 0 && state.traceMsgs.isEmpty
    | _ => false
  let unsupported := match MACRO_ENTRY sampleLeaf sampleContext default with
    | .error .unsupportedSyntax state => state.macroScope == 0 && state.traceMsgs.isEmpty
    | _ => false
  let scopedOk := match scopedMacro sampleLeaf sampleContext default with
    | .ok out state => leafExact out && state.macroScope == 1 && state.traceMsgs.isEmpty
    | _ => false
  let diagnostic := match errorMacro sampleLeaf sampleContext default with
    | .error (.error ref msg) state => leafExact ref && msg == "λ\x00error" && state.macroScope == 0 && state.traceMsgs.isEmpty
    | _ => false
  let scopeFirst := match CONTEXT_ENTRY contextInput sampleContext default with
    | .ok out state => branchExact out && state.macroScope == 0 && state.traceMsgs.isEmpty
    | _ => false
  let scopeSecond := match CONTEXT_ENTRY contextInput { sampleContext with currMacroScope := 18 } default with
    | .ok out state => leafExact out && state.macroScope == 0 && state.traceMsgs.isEmpty
    | _ => false
  let fields := match contextFields sampleLeaf sampleContext default with
    | .ok out state => contextNodeExact `Main out && state.macroScope == 0 && state.traceMsgs.isEmpty
    | _ => false
  let other := match contextFields sampleLeaf { sampleContext with quotContext := `Other, currRecDepth := 3 } default with
    | .ok out state => contextNodeExact `Other out && state.macroScope == 0 && state.traceMsgs.isEmpty
    | _ => false
  let depth := match contextFields sampleLeaf { sampleContext with currRecDepth := 512 } default with
    | .ok out state => leafExact out && state.macroScope == 0 && state.traceMsgs.isEmpty
    | _ => false
  [first, second, unsupported, scopedOk, diagnostic, scopeFirst, scopeSecond, fields, other, depth]

def emptyNodeExact (expected : Lean.Name) : Lean.Syntax → Bool
  | .node .none kind args => kind == expected && args.isEmpty
  | _ => false
def singletonLeafExact (expected : Lean.Name) : Lean.Syntax → Bool
  | .node .none kind args => kind == expected && args.size == 1 && leafExact args[0]!
  | _ => false
def syntheticNodeExact (expected : Lean.Name) : Lean.Syntax → Bool
  | .node (.synthetic start stop canonical) kind args =>
    start.byteIdx == 1 && stop.byteIdx == 3 && canonical &&
    kind == expected && args.size == 1 && leafExact args[0]!
  | _ => false
def inspectResult (macroFn : Lean.Syntax → Lean.MacroM Lean.Syntax)
    (input : Lean.Syntax) (check : Lean.Syntax → Bool) : Bool :=
  match macroFn input sampleContext default with
  | .ok output state => check output && state.macroScope == 0 && state.traceMsgs.isEmpty
  | _ => false
#eval show List Bool from
  let atom := Lean.Syntax.atom .none "A.B\x00🙂"
  let identAtom := Lean.Syntax.atom .none "ident"
  let original := Lean.Syntax.node (.synthetic ⟨1⟩ ⟨3⟩ true) `branch #[sampleLeaf]
  [inspectResult inspectSyntaxMacro .missing (emptyNodeExact `missing),
   inspectResult idSyntaxMacro .missing (emptyNodeExact .anonymous),
   inspectResult replaceSyntaxKindMacro .missing (fun | .missing => true | _ => false),
   inspectResult inspectSyntaxMacro sampleLeaf (singletonLeafExact (Lean.Name.num `Main._hyg 17)),
   inspectResult idSyntaxMacro sampleLeaf (emptyNodeExact (Lean.Name.num `Main._hyg 17)),
   inspectResult replaceSyntaxKindMacro sampleLeaf leafExact,
   inspectResult inspectSyntaxMacro atom (emptyNodeExact (Lean.Name.mkStr1 "A.B\x00🙂")),
   inspectResult idSyntaxMacro atom (emptyNodeExact .anonymous),
   inspectResult replaceSyntaxKindMacro atom (fun | .atom .none s => s == "A.B\x00🙂" | _ => false),
   inspectResult inspectSyntaxMacro original (singletonLeafExact `branch),
   inspectResult idSyntaxMacro original (singletonLeafExact .anonymous),
   inspectResult replaceSyntaxKindMacro original (syntheticNodeExact `renamed),
   inspectResult inspectSyntaxMacro identAtom (emptyNodeExact `ident),
   inspectResult idSyntaxMacro identAtom (emptyNodeExact .anonymous),
   inspectResult replaceSyntaxKindMacro identAtom (fun | .atom .none s => s == "ident" | _ => false)]
def scopeInput (value : Lean.Name) : Lean.Syntax :=
  match sampleLeaf with
  | .ident info raw _ pre => .ident info raw value pre
  | _ => .missing
def scopeExact (expected : Lean.Name) : Lean.Syntax → Bool
  | .ident info raw value pre => value == expected &&
      leafExact (.ident info raw (Lean.Name.num `Main._hyg 17) pre)
  | _ => false
def scopeBump : Nat → Lean.MacroM Unit
  | 0 => pure ()
  | n + 1 => Lean.Macro.withFreshMacroScope (scopeBump n)
def scopeState : Lean.Macro.State :=
  match (do scopeBump 10; Lean.Macro.trace `Trace "opaque\x00λ") sampleContext default with
  | .ok _ state => state
  | .error _ state => state
def scopeStateExact (counter : Nat) (state : Lean.Macro.State) : Bool :=
  state.macroScope == counter && state.traceMsgs == [(`Trace, "opaque\x00λ")]
def scopeBase : Lean.Name :=
  .str (.str (.str .anonymous "α") "_@") "Main"
def scopeName (counter : Nat) : Lean.Name := .num (.str scopeBase "_hyg") counter
#eval show List Bool from
  let plain := scopeInput `α
  let attached := match attachScopeMacro plain sampleContext scopeState with
    | .ok output state => scopeExact (scopeName 17) output && scopeStateExact 10 state
    | _ => false
  let first := freshIdentifierMacro plain sampleContext scopeState
  let firstOk := match first with
    | .ok output state => scopeExact (scopeName 10) output && scopeStateExact 11 state
    | _ => false
  let second := match first with
    | .ok output state => freshIdentifierMacro output sampleContext state
    | .error error state => .error error state
  let secondOk := match second with
    | .ok output state => scopeExact (.num (scopeName 10) 11) output && scopeStateExact 12 state
    | _ => false
  let changed := match second with
    | .ok input state =>
      let expected := Lean.Name.num (.str (.str (.str (.num (.num scopeBase 10) 11) "Other") "Module") "_hyg") 99
      match attachScopeMacro input { sampleContext with quotContext := `Other.Module, currMacroScope := 99 } state with
      | .ok output state => scopeExact expected output && scopeStateExact 12 state
      | _ => false
    | _ => false
  let atom := match attachScopeMacro (.atom .none "unchanged") sampleContext scopeState with
    | .ok (.atom .none "unchanged") state => scopeStateExact 10 state
    | _ => false
  [attached, firstOk, secondOk, changed, atom]

def positionOutputExact (start stop : Option Nat) : Lean.Syntax → Bool
  | .node .none kind args =>
    let one (expected : Option Nat) (label : String) (actual : Lean.Syntax) :=
      match expected, actual with
      | none, .missing => true
      | some p, .atom (.synthetic first last canonical) text =>
        first.byteIdx == p && last.byteIdx == p && canonical && text == label
      | _, _ => false
    kind == `positions && args.size == 2 && one start "start" args[0]! && one stop "end" args[1]!
  | _ => false
def checkPositions (input : Lean.Syntax)
    (all canonical info canonicalInfo : Option Nat × Option Nat) : Bool :=
  inspectResult syntaxPositionsMacro input (positionOutputExact all.1 all.2) &&
  inspectResult canonicalSyntaxPositionsMacro input (positionOutputExact canonical.1 canonical.2) &&
  inspectResult infoPositionsMacro input (positionOutputExact info.1 info.2) &&
  inspectResult canonicalInfoPositionsMacro input (positionOutputExact canonicalInfo.1 canonicalInfo.2)
#eval show List Bool from
  let known := (some 1, some 3)
  let absent := (none, none)
  let synthetic := (some 0, some 4)
  let tailOnly := (none, some 3)
  let noInfo := Lean.Syntax.atom .none "none"
  [checkPositions sampleLeaf known known known known,
   checkPositions .missing absent absent absent absent,
   checkPositions (.atom (.synthetic ⟨0⟩ ⟨4⟩ false) "synthetic") synthetic absent synthetic absent,
   checkPositions (.node .none `outer #[.missing, sampleLeaf, noInfo]) known known known known,
   checkPositions (.node .none `outer #[noInfo, sampleLeaf]) tailOnly tailOnly absent absent,
   checkPositions (.node (.synthetic ⟨0⟩ ⟨4⟩ false) `outer #[sampleLeaf]) synthetic tailOnly synthetic absent]

def referenceAtomExact (expected : Option (Nat × Nat × Bool)) : Lean.Syntax → Bool
  | .atom info text =>
    text == "reference\x00λ" && match expected, info with
      | none, .none => true
      | some (start, stop, canonical), .synthetic actualStart actualStop actualCanonical =>
        actualStart.byteIdx == start && actualStop.byteIdx == stop && actualCanonical == canonical
      | _, _ => false
  | _ => false
def checkReferenceAtoms (input : Lean.Syntax)
    (ordinary preferred : Option (Nat × Nat × Bool)) : Bool :=
  inspectResult referenceInfoMacro input (referenceAtomExact ordinary) &&
  inspectResult canonicalReferenceInfoMacro input (referenceAtomExact preferred) &&
  inspectResult atomFromMacro input (referenceAtomExact ordinary) &&
  inspectResult canonicalAtomFromMacro input (referenceAtomExact preferred)
def plainAtomExact (expected : String) : Lean.Syntax → Bool
  | .atom .none text => text == expected
  | _ => false
#eval show List Bool from
  let noncanonical := Lean.SourceInfo.synthetic ⟨0⟩ ⟨4⟩ false
  let synthetic := some (0, 4, false)
  [checkReferenceAtoms sampleLeaf (some (1, 3, false)) (some (1, 3, true)),
   checkReferenceAtoms .missing none none,
   checkReferenceAtoms (.atom .none "none") none none,
   checkReferenceAtoms (.atom noncanonical "synthetic") synthetic synthetic,
   checkReferenceAtoms (.node noncanonical `outer #[sampleLeaf]) synthetic synthetic,
   checkReferenceAtoms (.node .none `outer #[.atom .none "no head", sampleLeaf]) none none,
   checkReferenceAtoms (.node .none `outer #[sampleLeaf, .atom noncanonical "last"])
     (some (1, 4, false)) (some (1, 3, true)),
   checkReferenceAtoms (.node .none `outer #[.atom noncanonical "first", sampleLeaf])
     (some (0, 3, false)) (some (0, 3, false)),
   inspectResult atomMacro sampleLeaf (plainAtomExact "") &&
   inspectResult atomMacro (.atom noncanonical "λ\x00🙂") (plainAtomExact "λ\x00🙂") &&
   inspectResult atomMacro .missing (plainAtomExact "")]

def referenceScopeExact (check : Lean.Syntax → Bool) : Lean.Syntax → Bool
  | .node .none kind args => kind == `refs && args.size == 3 &&
    leafExact args[0]! && check args[1]! && leafExact args[2]!
  | _ => false
def publicErrorExact (macroFn : Lean.Syntax → Lean.MacroM Lean.Syntax)
    (input : Lean.Syntax) (check : Lean.Syntax → Bool) : Bool :=
  match macroFn input sampleContext scopeState with
  | .error (.error ref msg) state => check ref && msg == "public\x00λ" && scopeStateExact 10 state
  | _ => false
def checkReferenceSelection (input : Lean.Syntax) (check : Lean.Syntax → Bool) : Bool :=
  let scopedResult := match referenceScopeMacro input sampleContext scopeState with
    | .ok output state => referenceScopeExact check output && scopeStateExact 10 state
    | _ => false
  scopedResult && publicErrorExact publicErrorAtMacro input check
def zeroPositionExact : Lean.Syntax → Bool
  | .atom (.synthetic start stop canonical) text =>
    start.byteIdx == 0 && stop.byteIdx == 4 && !canonical && text == "positioned"
  | _ => false
def skippedReferenceExact : Lean.Syntax → Bool
  | .node .none kind args => kind == `skipped && args.size == 2 &&
    args[0]!.isMissing && zeroPositionExact args[1]!
  | _ => false
#eval show List Bool from
  let positioned := Lean.Syntax.atom (.synthetic ⟨0⟩ ⟨4⟩ false) "positioned"
  let guardSuccess := [publicErrorMacro, publicUnsupportedMacro].all fun macroFn =>
    match macroFn sampleLeaf sampleContext scopeState with
    | .ok output state => leafExact output && scopeStateExact 10 state
    | _ => false
  let unsupported := match publicUnsupportedMacro .missing sampleContext scopeState with
    | .error .unsupportedSyntax state => scopeStateExact 10 state
    | _ => false
  [checkReferenceSelection .missing leafExact,
   checkReferenceSelection (.node .none `empty #[]) leafExact,
   checkReferenceSelection (.node .none `headNone #[.atom .none "none", sampleLeaf]) leafExact,
   checkReferenceSelection positioned zeroPositionExact,
   checkReferenceSelection sampleLeaf leafExact,
   checkReferenceSelection (.node .none `skipped #[.missing, positioned]) skippedReferenceExact,
   guardSuccess, publicErrorExact publicErrorMacro .missing leafExact, unsupported]
"#;
