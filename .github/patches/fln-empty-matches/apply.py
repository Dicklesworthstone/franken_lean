"""Apply the reviewed empty-match implementation in an isolated runner checkout.

No fuzzy replacements, file deletion, history rewrite or unrelated edits. A changed
anchor is a hard stop; the workflow tests the resulting tree before publishing it.
"""
from pathlib import Path
import sys

PAYLOAD = Path(__file__).resolve().parent
TEST = Path('crates/fln/tests/source_nomatch.rs')
HELPER = Path('crates/fln-elab/src/source/matching/nomatch.rs')
SOURCE = Path('crates/fln-elab/src/source.rs')
MATCHING = Path('crates/fln-elab/src/source/matching.rs')


def new_file(path: Path, payload: str) -> None:
    if path.exists():
        raise RuntimeError(f'refusing to overwrite existing {path}')
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload, encoding='utf-8')


def replace_once(text: str, old: str, new: str) -> str:
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f'expected one anchor, found {count}: {old[:120]!r}')
    return text.replace(old, new, 1)


def main() -> None:
    if sys.argv[1:] == ['tests']:
        new_file(TEST, (PAYLOAD / 'source_nomatch.rs').read_text())
        return
    if sys.argv[1:] != ['implementation']:
        raise SystemExit('usage: apply.py tests|implementation')
    source = SOURCE.read_text()
    source = replace_once(source,
        "            MatchDiscriminant(matching::MatchParts<'a>, Option<Expr>),\n",
        "            MatchDiscriminant(matching::MatchParts<'a>, Option<Expr>),\n"
        "            NomatchDiscriminant(matching::MatchParts<'a>, Option<Expr>),\n")
    anchor = '                                if kind == &parser_kind(&["Term", "match"])\n'
    source = replace_once(source, anchor,
        '                                if kind == &parser_kind(&["Term", "nomatch"]) {\n'
        '                                    let parts = self.nomatch_parts(syntax)?;\n'
        '                                    let discriminant = parts.discriminant;\n'
        '                                    tasks.push(Task::NomatchDiscriminant(parts, expected));\n'
        '                                    tasks.push(Task::Visit(discriminant, None, true));\n'
        '                                    continue;\n'
        '                                }\n' + anchor)
    anchor = '                        Task::MatchDiscriminant(parts, expected) => {\n'
    source = replace_once(source, anchor,
        '                        Task::NomatchDiscriminant(parts, expected) => {\n'
        '                            let major = values.pop().expect("empty match discriminant visit");\n'
        '                            // Empty matches require checked branch equations, even\n'
        '                            // inside a structurally recursive definition.\n'
        '                            tasks.push(Task::Proof(self.start_refined_match(\n'
        '                                parts, major, expected, false,\n'
        '                            )?));\n'
        '                        }\n' + anchor)
    matching = replace_once(MATCHING.read_text(), 'mod mutual;\n', 'mod mutual;\nmod nomatch;\n')
    if HELPER.exists():
        raise RuntimeError(f'refusing to overwrite existing {HELPER}')
    new_file(HELPER, (PAYLOAD / 'nomatch.rs').read_text())
    SOURCE.write_text(source)
    MATCHING.write_text(matching)


if __name__ == '__main__':
    main()
