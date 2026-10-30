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
    let fixture = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../fln-olean/fixtures/ir/NativeMacroModule.lean"
    ));
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
    assert!(
        compile(
            std::slice::from_ref(&module),
            &name("namespaceMacro"),
            &VerifiedPartition::user_fixture(),
            &users,
            IrExecutionLimits::default()
        )
        .is_err()
    );

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
        b"[true, true, true, true, true, true, true, true, true, true]\n[true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]\n"
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
"#;
