from pathlib import Path
import shutil
import sys

PAYLOAD = Path(__file__).resolve().parent

def replace(text, old, new):
    if text.count(old) != 1:
        raise RuntimeError(f'changed source anchor: {old[:140]!r} ({text.count(old)})')
    return text.replace(old, new)

def tests():
    test = Path('crates/fln/tests/source_rcases.rs')
    fixture = Path('crates/fln/tests/fixtures/rcases.tsv')
    if test.exists() or fixture.exists():
        raise RuntimeError('rcases test already exists')
    text = Path('crates/fln/tests/source_empty_matrices.rs').read_text()
    text = replace(text, 'assert_eq!(counts, [18, 10]);', 'assert_eq!(counts, [14, 9]);')
    text = text.replace('empty_matrices', 'rcases').replace('EMPTY_MATRIX', 'RCASES')
    text = text.replace('["Init", "Core"]', '["Init", "RCases"]').replace('<= 32', '<= 64')
    test.write_text(text)
    shutil.copyfile(PAYLOAD / 'cases.tsv', fixture)

def implementation():
    destination = Path('crates/fln-elab/src/source/tactics/rcases.rs')
    if destination.exists():
        raise RuntimeError('rcases implementation already exists')
    shutil.copyfile(PAYLOAD / 'rcases.rs', destination)
    path = Path('crates/fln-elab/src/source/tactics.rs')
    text = path.read_text()
    text = replace(text, 'mod refine;\n', 'mod refine;\nmod rcases;\n')
    text = replace(text, '            } else if kind == &parser_kind(&["Tactic", "refine"]) {',
        '            } else if kind == &parser_kind(&["Tactic", "rcases"]) {\n                self.rcases_proof_goal(proof, goal, args)?;\n            } else if kind == &parser_kind(&["Tactic", "refine"]) {')
    path.write_text(text)
    path = Path('crates/fln-elab/src/source/tactics/eliminate.rs')
    text = path.read_text()
    text = replace(text, '    EmptyMatrix(HashMap<Name, Vec<Name>>),', '    EmptyMatrix(HashMap<Name, Vec<Name>>),\n    /// Recursive tactic patterns retain the ordinary cases removal semantics.\n    RCases(HashMap<Name, Vec<Name>>),')
    text = replace(text, '            EliminationSyntax::EmptyMatrix(_) => (Name::anonymous(), &[][..], false, &[][..]),',
        '            EliminationSyntax::EmptyMatrix(_) | EliminationSyntax::RCases(_) => (Name::anonymous(), &[][..], false, &[][..]),')
    text = replace(text, '                    source_match: !matches!(input, EliminationSyntax::Tactic(_)),',
        '                    source_match: !matches!(input, EliminationSyntax::Tactic(_) | EliminationSyntax::RCases(_)),')
    text = replace(text, '                        EliminationSyntax::EmptyMatrix(fields) => {',
        '                        EliminationSyntax::EmptyMatrix(fields) | EliminationSyntax::RCases(fields) => {')
    path.write_text(text)

{'tests': tests, 'implementation': implementation}[sys.argv[1]]()
