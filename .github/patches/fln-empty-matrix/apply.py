"""Extend checked empty matches without modifying the checking engines."""
from pathlib import Path

PAYLOAD = Path(__file__).resolve().parent


def replace(text, old, new):
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f'expected exactly one source anchor, found {count}: {old[:100]!r}')
    return text.replace(old, new, 1)


def main():
    source_path = Path('crates/fln-elab/src/source.rs')
    tactics_path = Path('crates/fln-elab/src/source/tactics.rs')
    eliminate_path = Path('crates/fln-elab/src/source/tactics/eliminate.rs')
    helper = Path('crates/fln-elab/src/source/tactics/empty.rs')
    tests = Path('crates/fln/tests/source_empty_matrices.rs')
    fixtures = Path('crates/fln/tests/fixtures/empty_matrices.tsv')
    previous = Path('crates/fln/tests/source_nomatch.rs')
    if helper.exists() or tests.exists() or fixtures.exists():
        raise RuntimeError('the empty matrix implementation is already present')
    source = source_path.read_text()
    source = replace(source,
        "            NomatchDiscriminant(matching::MatchParts<'a>, Option<Expr>),\n",
        "            NomatchDiscriminant(Arguments<'a>, Vec<Typed>, Option<Expr>),\n")
    source = replace(source, '''                                if kind == &parser_kind(&["Term", "nomatch"]) {
                                    let parts = self.nomatch_parts(syntax)?;
                                    let discriminant = parts.discriminant;
                                    tasks.push(Task::NomatchDiscriminant(parts, expected));
                                    tasks.push(Task::Visit(discriminant, None, true));
                                    continue;
                                }
''', '''                                if kind == &parser_kind(&["Term", "nofun"]) {
                                    tasks.push(Task::Proof(self.start_empty_function(syntax, expected)?));
                                    continue;
                                }
                                if kind == &parser_kind(&["Term", "nomatch"]) {
                                    let items = self.nomatch_discriminants(syntax)?;
                                    let arguments = Arguments::Separated(items, &[","]);
                                    let (first, remaining) = arguments.split_first().expect("nonempty discriminants");
                                    tasks.push(Task::NomatchDiscriminant(remaining, Vec::new(), expected));
                                    tasks.push(Task::Visit(first, None, true));
                                    continue;
                                }
''')
    start = source.index('                        Task::NomatchDiscriminant(')
    end = source.index('                        Task::MatchDiscriminant(', start)
    old = source[start:end]
    if 'self.start_refined_match(' not in old:
        raise RuntimeError('unexpected empty-match continuation')
    source = replace(source, old, '''                        Task::NomatchDiscriminant(remaining, mut terms, expected) => {
                            terms.push(values.pop().expect("empty match discriminant visit"));
                            if let Some((next, rest)) = remaining.split_first() {
                                tasks.push(Task::NomatchDiscriminant(rest, terms, expected));
                                tasks.push(Task::Visit(next, None, true));
                            } else {
                                tasks.push(Task::Proof(self.start_empty_match(terms, expected)?));
                            }
                        }
''')
    tactics = replace(tactics_path.read_text(), 'mod equality;\n', 'mod equality;\nmod empty;\n')
    elimination = replace(eliminate_path.read_text(),
        "    RecursiveMatch(matching::MatchParts<'a>),\n",
        "    RecursiveMatch(matching::MatchParts<'a>),\n"
        "    /// Retain each live branch as another empty-matrix obligation.\n"
        "    EmptyMatrix,\n")
    elimination = replace(elimination, '''            EliminationSyntax::Match(_) | EliminationSyntax::RecursiveMatch(_) => {
                (Name::anonymous(), &[][..], true, &[][..])
            }
''', '''            EliminationSyntax::Match(_) | EliminationSyntax::RecursiveMatch(_) => {
                (Name::anonymous(), &[][..], true, &[][..])
            }
            EliminationSyntax::EmptyMatrix => (Name::anonymous(), &[][..], false, &[][..]),
''')
    elimination = replace(elimination,
        '            if matches!(input, EliminationSyntax::Match(_))\n',
        '            if matches!(input, EliminationSyntax::Match(_) | EliminationSyntax::EmptyMatrix)\n')
    matching = Path('crates/fln-elab/src/source/matching/nomatch.rs')
    if "fn nomatch_parts<" not in matching.read_text():
        raise RuntimeError('unexpected single-column parser')
    single = (PAYLOAD / 'nomatch.rs').read_text()
    baseline_tests = replace(previous.read_text(),
        '"def bad (h : False) : Nat := nomatch h, true",',
        '"def bad (n : Nat) (b : Bool) : Nat := nomatch n, b",')
    for path, contents in [(source_path, source), (tactics_path, tactics),
                           (eliminate_path, elimination), (matching, single),
                           (helper, (PAYLOAD / 'empty.rs').read_text()),
                           (previous, baseline_tests),
                           (fixtures, (PAYLOAD / 'empty_matrices.tsv').read_text()),
                           (tests, (PAYLOAD / 'source_empty_matrices.rs').read_text())]:
        path.write_text(contents)


if __name__ == '__main__':
    main()
