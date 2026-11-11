//! Real user IR calling native source queries, compared with the exact pinned
//! Lean runtime on complete syntax values and every Macro.State field.
use super::sequences_reference::{ORACLE, lean_syntax};
use super::*;
use fln_syntax::tree::RawIdentifier;
use std::{collections::BTreeMap, path::PathBuf, process::Command};

#[test]
fn live_pinned_syntax_source_queries_preserve_positions_spelling_and_macro_state() {
    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for syntax source queries"
        );
        eprintln!("SKIP: native syntax source queries require FLN_REFERENCE_LEAN");
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
        .join(format!(
            "source-query-macro-{}-{unique}",
            std::process::id()
        ));
    std::fs::create_dir_all(&dir).unwrap();
    let fixture = include_str!("../../../../fln-olean/fixtures/ir/SourceQueryMacroModule.lean");
    std::fs::write(dir.join("SourceQueryMacroModule.lean"), fixture).unwrap();
    let emitted = Command::new(&reference)
        .current_dir(&dir)
        .args([
            "-j1",
            "-o",
            "SourceQueryMacroModule.olean",
            "SourceQueryMacroModule.lean",
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
        &std::fs::read(dir.join("SourceQueryMacroModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .filter_map(|declaration| match declaration {
            IrDecl::Function { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    let macros: BTreeMap<_, _> = [
        "immediateInfoMacro",
        "headInfoMacro",
        "rangeMacro",
        "canonicalRangeMacro",
        "hasMissingMacro",
        "reprintMacro",
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
    let mut rows = BTreeSet::new();
    let mut checks = Vec::new();
    for (entry, input, expected) in cases() {
        let report = macros[entry].execute(
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
                .all(|function| function.producer() == "reference"
                    && users.contains(&function.name)
                    && !function.name.to_display_string().starts_with("Lean.")),
            "only the user fixture may execute interpreted IR: {entry}"
        );
        let Outcome::Complete(Ok(MacroResult::Expanded {
            syntax,
            state: next,
        })) = report.outcome
        else {
            panic!("{entry} on {input:?}: {:?}; {dir:?}", report.outcome);
        };
        assert_eq!(syntax, expected, "{entry} on {input:?}");
        assert_eq!(next, state, "all three state fields survive {entry}");
        checks.push(format!(
            "checkSequence {entry} ({}) ({})",
            lean_syntax(&input),
            lean_syntax(&expected)
        ));
    }
    for row in [
        "mirror:Lean.Syntax.getInfo?",
        "mirror:Lean.Syntax.getHeadInfo?",
        "mirror:Lean.Syntax.getRange?",
        "mirror:Lean.Syntax.hasMissing",
        "mirror:Lean.Syntax.reprint",
    ] {
        assert!(rows.contains(row), "actual user IR missed {row}");
    }
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
        "native and pinned syntax source queries: {} complete syntax/state cases",
        checks.len()
    );
}

fn atom(text: &str) -> Syntax {
    atom_with(SourceInfo::None, text)
}

fn atom_with(info: SourceInfo, text: &str) -> Syntax {
    Syntax::Atom {
        info,
        val: text.into(),
    }
}

fn synthetic(start: usize, stop: usize, canonical: bool) -> SourceInfo {
    SourceInfo::Synthetic {
        pos: BytePos(start),
        end_pos: BytePos(stop),
        canonical,
    }
}

fn range(start: usize, stop: usize) -> Syntax {
    atom_with(synthetic(start, stop, true), "range")
}

fn choice(args: Vec<Syntax>) -> Syntax {
    Syntax::node(name("choice"), args)
}

fn cases() -> Vec<(&'static str, Syntax, Syntax)> {
    let mut cases = Vec::new();
    let empty = Syntax::node(name("empty"), vec![]);
    let own_info = synthetic(0, 4, false);
    let located = Syntax::Node {
        info: own_info,
        kind: name("outer"),
        args: vec![leaf()],
    };
    let nested = Syntax::node(name("nested"), vec![Syntax::Missing, empty.clone(), leaf()]);
    let first_without_info = Syntax::node(name("nested"), vec![atom("first"), leaf()]);
    for input in [
        Syntax::Missing,
        empty.clone(),
        leaf(),
        located.clone(),
        nested.clone(),
        first_without_info.clone(),
    ] {
        let expected = if matches!(input, Syntax::Missing) {
            Syntax::Missing
        } else {
            atom_with(input.info(), "info")
        };
        cases.push(("immediateInfoMacro", input, expected));
    }
    for (input, expected) in [
        (Syntax::Missing, Syntax::Missing),
        (empty.clone(), Syntax::Missing),
        (leaf(), atom_with(leaf().info(), "info")),
        (located.clone(), atom_with(own_info, "info")),
        (nested.clone(), atom_with(leaf().info(), "info")),
        (first_without_info.clone(), atom("info")),
    ] {
        cases.push(("headInfoMacro", input, expected));
    }
    let mixed = Syntax::node(
        name("mixed"),
        vec![
            leaf(),
            atom("gap"),
            atom_with(synthetic(0, 4, false), "tail"),
        ],
    );
    for (input, normal, canonical) in [
        (Syntax::Missing, Syntax::Missing, Syntax::Missing),
        (empty.clone(), Syntax::Missing, Syntax::Missing),
        (leaf(), range(1, 3), range(1, 3)),
        (located, range(0, 4), Syntax::Missing),
        (nested, range(1, 3), range(1, 3)),
        (first_without_info, Syntax::Missing, Syntax::Missing),
        (mixed, range(1, 4), range(1, 3)),
        (
            atom_with(synthetic(0, 4, true), "canonical"),
            range(0, 4),
            range(0, 4),
        ),
    ] {
        cases.push(("rangeMacro", input.clone(), normal));
        cases.push(("canonicalRangeMacro", input, canonical));
    }
    for (input, expected) in [
        (Syntax::Missing, true),
        (empty.clone(), false),
        (leaf(), false),
        (
            Syntax::node(name("complete"), vec![atom("x"), empty.clone()]),
            false,
        ),
        (
            Syntax::node(name("incomplete"), vec![atom("x"), Syntax::Missing]),
            true,
        ),
        (choice(vec![atom("first"), Syntax::Missing]), true),
    ] {
        cases.push((
            "hasMissingMacro",
            input,
            atom(if expected { "true" } else { "false" }),
        ));
    }
    let owned_ident = Syntax::Ident {
        info: synthetic(1, 3, true),
        raw_val: RawIdentifier::owned("xλy".into(), span(1, 3)).unwrap(),
        val: name("Resolved.value"),
        preresolved: vec![Preresolved::Namespace {
            ns: name("Resolved"),
        }],
    };
    let agreeing = choice(vec![
        atom("x"),
        Syntax::node(name("wrapper"), vec![atom("x")]),
    ]);
    for (input, expected) in [
        (Syntax::Missing, atom("")),
        (empty, atom("")),
        (leaf(), atom(" α ")),
        (owned_ident, atom(" λ ")),
        (atom("λ\0"), atom(" λ\0 ")),
        (
            Syntax::Node {
                info: own_info,
                kind: name("root"),
                args: vec![leaf(), atom("+")],
            },
            atom(" α  + "),
        ),
        (agreeing.clone(), atom(" x ")),
        (choice(vec![agreeing, atom("x")]), atom(" x ")),
        (choice(vec![atom("x"), atom("y")]), Syntax::Missing),
        (
            choice(vec![choice(vec![atom("x"), atom("y")]), atom("x")]),
            Syntax::Missing,
        ),
    ] {
        cases.push(("reprintMacro", input, expected));
    }
    cases
}
