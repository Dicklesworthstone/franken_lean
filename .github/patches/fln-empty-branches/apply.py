"""Apply only the checked empty-branch feature; refuse ambiguous/stale anchors."""
from pathlib import Path
import shutil
import subprocess
import sys

PAYLOAD = Path(__file__).resolve().parent
ROOT = Path.cwd()


def replace(text, old, new, count=1):
    found = text.count(old)
    if found != count:
        raise RuntimeError(f'expected {count} occurrences, found {found}: {old[:120]!r}')
    return text.replace(old, new)


def tests():
    target = ROOT / 'crates/fln/tests/source_empty_branches.rs'
    fixture = ROOT / 'crates/fln/tests/fixtures/empty_branches.tsv'
    if target.exists() or fixture.exists():
        raise RuntimeError('test paths already exist; refusing to replace them')
    template = (ROOT / 'crates/fln/tests/source_empty_matrices.rs').read_text()
    template = replace(template, 'assert_eq!(counts, [18, 10]);', 'assert_eq!(counts, [19, 12]);')
    # The production seed intentionally has no Exists. Exercise it by admitting
    # the ordinary polymorphic source declaration in this test alone; the other
    # test still uses the unmodified, actual imported Init.Core declaration.
    template = replace(template, '    verify(&engine, STACK);\n}\n', r'''    let engine = engine
        .check_source_files(
            &[b"universe u\ninductive Exists {A : Sort u} (p : A -> Prop) : Prop where | intro (w : A) (h : p w)"],
            &KVMap::new(),
            SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))),
        )
        .expect("admit the ordinary Exists declaration for the minimal-seed fixture")
        .into_complete()
        .expect("both checkers admit Exists")
        .engine;
    verify(&engine, STACK);
}
''')
    template = template.replace('empty_matrices', 'empty_branches').replace('EMPTY_MATRIX', 'EMPTY_BRANCH')
    target.write_text(template)
    shutil.copyfile(PAYLOAD / 'cases.tsv', fixture)


def implementation():
    path = ROOT / 'crates/fln-elab/src/source/tactics/empty.rs'
    actual = subprocess.check_output(['git', 'hash-object', str(path)], text=True).strip()
    if actual != '7fbb2351889abcf89c985e4276fea73735a3d977':
        raise RuntimeError(f'empty compiler changed concurrently: {actual}')
    text = path.read_text()
    text = replace(text, 'use fln_env::constants::ConstantInfo;',
                   'use fln_env::constants::{ConstantInfo, InductiveVal};')
    text = replace(text, 'use std::collections::HashSet;',
                   'use std::collections::{HashMap, HashSet, VecDeque};')
    text = replace(text, 'Split(ProofGoal, usize),', 'Split(ProofGoal, VecDeque<Name>),')
    head, tail = text.split("    fn solve_empty_matrix<'a>(", 1)
    assert 'let mut pending = vec![EmptyTask::Split(goal, 0)];' in tail
    text = head + (PAYLOAD / 'solve.rs').read_text()
    text = text.replace('//! as another obligation; running out of columns with any live goal refuses.',
                        '//! as another obligation. Nonrecursive constructor fields become new columns.')
    path.write_text(text)

    path = ROOT / 'crates/fln-elab/src/source/tactics/eliminate.rs'
    text = path.read_text()
    text = replace(text, '    EmptyMatrix,', '    EmptyMatrix(HashMap<Name, Vec<Name>>),')
    text = replace(text, '    source_match: bool,\n}',
                   "    source_match: bool,\n    empty_fields: Option<&'a [Name]>,\n}")
    text = replace(text, '            source_match,\n        } = context;',
                   '            source_match,\n            empty_fields,\n        } = context;')
    text = replace(text, 'let names = alternative.map_or(&[][..], |alt| alt.names.as_slice());',
                   'let names = alternative.map_or(empty_fields.unwrap_or(&[]), |alt| alt.names.as_slice());')
    text = replace(text, 'EliminationSyntax::EmptyMatrix', 'EliminationSyntax::EmptyMatrix(_)', 2)
    text = replace(text,
        '                    source_match: !matches!(input, EliminationSyntax::Tactic(_)),\n',
        '                    source_match: !matches!(input, EliminationSyntax::Tactic(_)),\n'
        '                    empty_fields: match input {\n'
        '                        EliminationSyntax::EmptyMatrix(fields) => {\n'
        '                            fields.get(&rule.ctor).map(Vec::as_slice)\n'
        '                        }\n'
        '                        _ => None,\n'
        '                    },\n')
    path.write_text(text)

    path = ROOT / 'crates/fln-elab/src/source/tactics/constructors.rs'
    text = replace(path.read_text(), '    fn empty_evidence(\n', '    pub(super) fn empty_evidence(\n')
    path.write_text(text)


if __name__ == '__main__':
    {'tests': tests, 'implementation': implementation}[sys.argv[1]]()
