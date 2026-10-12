from pathlib import Path
import sys

PAYLOAD = Path(__file__).resolve().parent

def replace(text, old, new):
    if text.count(old) != 1:
        raise RuntimeError(f'changed source anchor: {old[:140]!r} ({text.count(old)})')
    return text.replace(old, new)

def tests():
    destination = Path('crates/fln/tests/source_rintro_obtain.rs')
    fixture = Path('crates/fln/tests/fixtures/rintro_obtain.tsv')
    if destination.exists() or fixture.exists():
        raise RuntimeError('rintro/obtain test destinations already exist')
    text = Path('crates/fln/tests/source_rcases.rs').read_text()
    text = replace(text, 'assert_eq!(counts, [16, 11]);', 'assert_eq!(counts, [36, 23]);')
    text = replace(text, 'const FIXTURES: &str = include_str!("fixtures/rcases.tsv");',
        'const FIXTURES: &str = concat!(include_str!("fixtures/rcases.tsv"), "\\n", include_str!("fixtures/rintro_obtain.tsv"));')
    text = text.replace('rcases_and_functions_pass_both_checkers', 'recursive_introductions_and_obtained_witnesses_pass_both_checkers')
    text = text.replace('actual_imported_core_checks_the_same_rcases', 'actual_imported_rcases_checks_introductions_and_obtained_witnesses')
    text = text.replace('RCASES', 'RINTRO_OBTAIN')
    destination.write_text(text)
    fixture.write_text((PAYLOAD / 'cases.tsv').read_text())

def implementation():
    destination = Path('crates/fln-elab/src/source/tactics/rcases/derived.rs')
    if destination.exists():
        raise RuntimeError('rintro/obtain implementation already exists')
    destination.parent.mkdir(exist_ok=True)
    destination.write_text((PAYLOAD / 'derived.rs').read_text())
    path = Path('crates/fln-elab/src/source/tactics/rcases.rs')
    text = path.read_text()
    text = replace(text, 'use std::collections::HashMap;\n', 'use std::collections::HashMap;\nmod derived;\n')
    # Pattern syntax is consumed synchronously. Only existing goal/close
    # frames escape, so pattern borrows are independent of the outer proof.
    text = replace(text, "        args: &'a [Syntax],", '        args: &[Syntax],')
    text = replace(text, "        mut arena: Vec<Pattern<'a>>,", "        mut arena: Vec<Pattern<'_>>,")
    path.write_text(text)
    path = Path('crates/fln-elab/src/source/tactics.rs')
    text = path.read_text()
    anchor = '            } else if kind == &parser_kind(&["Tactic", "rcases"]) {'
    text = replace(text, anchor, '''            } else if kind == &parser_kind(&["Tactic", "rintro"]) {
                self.rintro_proof_goal(proof, goal, args)?;
            } else if kind == &parser_kind(&["Tactic", "obtain"]) {
                self.obtain_proof_goal(proof, goal, args)?;
''' + anchor)
    path.write_text(text)

{'tests': tests, 'implementation': implementation}[sys.argv[1]]()
