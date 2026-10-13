"""Integrate native severity routing without replacing unrelated source files."""
from pathlib import Path
import re

engine = "crates/fln/src/lib.rs"
cli = "crates/fln-cli/src/lib.rs"
if "guard_messages::Guards" in Path(cli).read_text() and "dropping error messages" in Path(engine).read_text():
    print("native guard filters already integrated")
    raise SystemExit(0)
changes = {}

def replace(path, old, new, count=1):
    text = changes.get(path, Path(path).read_text(encoding="utf-8"))
    if text.count(old) != count:
        raise RuntimeError(f"anchor count in {path}: wanted {count}, found {text.count(old)}: {old[:100]!r}")
    changes[path] = text.replace(old, new)

def replace_pattern(path, pattern, new):
    text = changes.get(path, Path(path).read_text(encoding="utf-8"))
    text, count = re.subn(pattern, lambda _: new, text)
    if count != 1:
        raise RuntimeError(f"pattern count in {path}: {count}: {pattern!r}")
    changes[path] = text

replace_pattern(engine, r'                        if !spec\.filters\.is_empty\(\) \{\s*return Err\(not_implemented\(\s*"`#guard_msgs` with a filtering specification",?\s*\)\);\s*\}', '''                        // We cannot recover and reproduce failed command diagnostics yet.
                        // Never implement `drop error` by ignoring a failed computation.
                        if spec.action(fln_parse::command_scope::guard_spec::Severity::Error)
                            == fln_parse::command_scope::guard_spec::Action::Drop
                        {
                            return Err(not_implemented("`#guard_msgs` dropping error messages"));
                        }''')
replace(cli, "mod guard_spec_tests;\n", "mod guard_spec_tests;\nmod guard_messages;\n#[cfg(test)]\nmod guard_filter_tests;\n")
replace(cli, "guarded: &mut std::collections::BTreeMap<usize, (Vec<String>, bool)>,",
    "guarded: &mut guard_messages::Guards<'_>,")
replace(cli, '''    if let Some((messages, _)) = guarded.get_mut(&warning.command_index) {
        messages.push(guard_message("warning", &warning.message));
        return Ok(());
    }''', '''    if let Some(guard) = guarded.get_mut(&warning.command_index)
        && guard.warning(&warning.message)
    {
        return Ok(());
    }''')
replace(cli, '''    let mut guarded: std::collections::BTreeMap<usize, (Vec<String>, bool)> = completed
        .guards
        .iter()
        .map(|guard| (guard.command_index, (Vec::new(), false)))
        .collect();''', '''    let mut guarded = guard_messages::Guards::new();
    for guard in &completed.guards {
        if guard.command_index >= completed.command_count || guarded.contains_key(&guard.command_index) {
            return source_failure("internal-fault", "duplicate or out-of-range message guard", false,
                SourcePresentation::Lean, 4);
        }
        // Defensive checks for callers retaining or constructing public batches.
        if guard.spec.positions || guard.spec.action(fln_parse::command_scope::guard_spec::Severity::Error)
            == fln_parse::command_scope::guard_spec::Action::Drop
        {
            return source_failure("capability", "message positions and dropping error messages are not implemented",
                false, SourcePresentation::Lean, CAPABILITY_NOT_IMPLEMENTED_EXIT);
        }
        guarded.insert(guard.command_index, guard_messages::Buffer::new(&guard.spec));
    }''')
replace(cli, '''                        let messages = guarded
                            .get_mut(&command_index)
                            .map(|(messages, _)| messages);''', '''                        let mut discarded = Vec::new();
                        let messages = match guarded.get_mut(&command_index) {
                            Some(guard) => guard.evaluation_target(&mut discarded),
                            None => None,
                        };''')
replace(cli, '''                if let Some((messages, _)) = guarded.get_mut(&command_index) {
                    // An IO action's output was written while it ran, not returned here.''',
'''                if let Some(guard) = guarded.get_mut(&command_index) {
                    // An IO action's output was written while it ran, not returned here.''')
replace(cli, '''                        Ok(line) => {
                            messages.push(guard_message("info", line.trim_end_matches('\\n')))
                        }''', '''                        Ok(line) => guard.info(&line, false, &mut stdout),''')
replace(cli, '''                if let Some((messages, from_check)) = guarded.get_mut(&command_index) {
                    messages.push(guard_message("info", line.trim_end_matches('\\n')));
                    *from_check = true;
                    continue;
                }''', '''                if let Some(guard) = guarded.get_mut(&command_index) {
                    guard.info(&line, true, &mut stdout);
                    continue;
                }''')
replace(cli, '''        let (messages, from_check) = guarded.remove(&guard.command_index).unwrap_or_default();
        let produced = guard.spec.combine(messages);''', '''        let Some(messages) = guarded.remove(&guard.command_index) else {
            return source_failure("internal-fault", "message guard lost its collector", false,
                SourcePresentation::Lean, 4);
        };
        let from_check = messages.from_check;
        let produced = guard.spec.combine(messages.checked);''')
replace("crates/fln/tests/source_guard_msgs.rs", "#guard_msgs (drop warning) in", "#guard_msgs (drop error) in")
replace("crates/fln-cli/tests/lean_guard_msgs.rs", "#guard_msgs (drop warning) in", "#guard_msgs (drop error) in")
replace("crates/fln-cli/tests/lean_guard_msgs.rs", '            "specification",', '            "dropping error",')
replace("crates/fln-cli/tests/lean_guard_msgs.rs", '//! - a `(…)` spec (it changes which messages are checked);',
    '//! - `drop error`, which needs command-error recovery, and position reporting;')
for path, text in changes.items():
    Path(path).write_text(text, encoding="utf-8")
    print(f"integrated {path}")
