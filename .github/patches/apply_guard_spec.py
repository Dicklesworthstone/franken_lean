"""Apply the narrowly anchored native guard-spec integration, atomically in memory.

This landing helper is idempotent; it never downloads code, changes the pin,
removes files, rewrites unrelated paths or weakens an existing guard refusal.
"""
from pathlib import Path

markers = {
    "crates/fln-parse/src/command_scope.rs": "pub mod guard_spec;",
    "crates/fln/src/lib.rs": "pub spec: fln_parse::command_scope::guard_spec::GuardSpec,",
    "crates/fln-cli/src/lib.rs": "guard.spec.matches(&guard.expected, &produced)",
    "crates/fln/tests/source_guard_msgs.rs": "spec: Default::default(),",
}
if all(marker in Path(path).read_text(encoding="utf-8") for path, marker in markers.items()):
    print("guard specification integration already present")
    raise SystemExit(0)

changes = {}

def replace(path, old, new):
    text = changes.get(path, Path(path).read_text(encoding="utf-8"))
    if old == new:
        raise RuntimeError("identical replacement")
    if new in text:
        return
    if old not in text:
        raise RuntimeError(f"missing integration anchor in {path}: {old[:120]!r}")
    if text.count(old) != 1:
        raise RuntimeError(f"ambiguous integration anchor in {path}: {old[:120]!r}")
    changes[path] = text.replace(old, new, 1)

parser = "crates/fln-parse/src/command_scope.rs"
replace(parser, "pub mod imports;\n", "pub mod imports;\npub mod guard_spec;\n")

engine = "crates/fln/src/lib.rs"
replace(engine, "pub struct SourceGuard {\n    pub command_index: usize,\n    pub expected: String,\n}",
"pub struct SourceGuard {\n    pub command_index: usize,\n    pub expected: String,\n    /// Parsed comparison/filter policy, retained for the presentation that judges messages.\n    pub spec: fln_parse::command_scope::guard_spec::GuardSpec,\n}")
replace(engine, '''                        if specified {
                            return Err(not_implemented("`#guard_msgs` with a specification"));
                        }''', '''                        let spec = if specified {
                            grammar.enter(|| fln_parse::command_scope::guard_spec::parse(command_source, body))
                                .map_err(|error| EngineExecutionError::BatchCommand {
                                    index: command_index,
                                    error: Box::new(EngineExecutionError::Frontend(
                                        DefinitionFrontendError::Parse(error),
                                    )),
                                    at: Some(original_offset),
                                })?
                        } else {
                            fln_parse::command_scope::guard_spec::GuardSpec::default()
                        };
                        if spec.positions {
                            return Err(not_implemented("`#guard_msgs` with message positions"));
                        }
                        if !spec.filters.is_empty() {
                            return Err(not_implemented("`#guard_msgs` with a filtering specification"));
                        }''')
replace(engine, '''                        guards.push(SourceGuard {
                            command_index,
                            expected,
                        });''', '''                        guards.push(SourceGuard {
                            command_index,
                            expected,
                            spec,
                        });''')
replace(engine, '''                    // A spec (`(drop …)`, `(whitespace := …)`, …) is not read, and a guard inside
                    // a guard would judge one command twice: both are refused, never ignored.''',
'''                    // Retain the parsed policy for the judge. A nested guard and unavailable
                    // message sources remain explicit capability refusals.''')

cli = "crates/fln-cli/src/lib.rs"
replace(cli, "mod source_evaluation;\n", "mod source_evaluation;\n#[cfg(test)]\nmod guard_spec_tests;\n")
replace(cli, '''    // The pin's `elabGuardMsgs`, default spec: the checked messages joined by `---\\n` and
    // ASCII-trimmed, compared with the expected text after `WhitespaceMode.normalized`
    // (line breaks become spaces). A pass prints nothing; a failure is the pin's error.''',
'''    // The pin sorts individual messages before joining and trimming, then applies the
    // selected whitespace and substring policy. No policy changes execution authority.''')
replace(cli, '''        let joined = messages.join("---\\n");
        let produced = joined.trim_ascii();
        if guard.expected.replace('\\n', " ") != produced.replace('\\n', " ") {''',
'''        let produced = guard.spec.combine(messages);
        if !guard.spec.matches(&guard.expected, &produced) {''')

engine_test = "crates/fln/tests/source_guard_msgs.rs"
replace(engine_test, '            expected: "info: 4".to_owned(),\n',
    '            expected: "info: 4".to_owned(),\n            spec: Default::default(),\n')

# Validate every anchor before modifying any file.
for path, text in changes.items():
    Path(path).write_text(text, encoding="utf-8")
    print(f"integrated {path}")
if not changes:
    print("guard specification integration already present")
