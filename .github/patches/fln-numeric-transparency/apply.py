"""Preserve the unreduced expected type of numeric instance goals."""
from pathlib import Path
import shutil
import sys

PAYLOAD = Path(__file__).resolve().parent


def replace(text, old, new):
    count = text.count(old)
    if count != 1:
        raise RuntimeError(f'expected one anchor, found {count}: {old[:120]!r}')
    return text.replace(old, new)


def tests():
    target = Path('crates/fln/tests/source_numeric_transparency.rs')
    fixture = Path('crates/fln/tests/fixtures/numeric_transparency.tsv')
    if target.exists() or fixture.exists():
        raise RuntimeError('test destinations already exist; refusing overwrite')
    text = Path('crates/fln/tests/source_empty_matrices.rs').read_text()
    text = replace(text, 'assert_eq!(counts, [18, 10]);', 'assert_eq!(counts, [8, 6]);')
    text = text.replace('empty_matrices', 'numeric_transparency')
    text = text.replace('EMPTY_MATRIX', 'NUMERIC_TRANSPARENCY')
    target.write_text(text)
    shutil.copyfile(PAYLOAD / 'cases.tsv', fixture)


def implementation():
    path = Path('crates/fln-elab/src/source/numeric.rs')
    text = path.read_text()
    text = replace(text, '''        let type_ = self.hole(binder_type.clone())?;
        if let Some(expected) = expected {
            self.constrain(&type_, expected)?;
        }
        self.numeric_argument(function, type_)
''', '''        // Keep the expected type's original head in the class obligation.
        // Assigning a fresh hole through ordinary conversion first can unfold
        // a semireducible value behind a projection (b.carrier) into Nat. That
        // invents an OfNat/OfScientific instance at instances transparency.
        // numeric_argument still checks its sort against the method's universe.
        let type_ = match expected {
            Some(expected) => self.instantiate(expected)?,
            None => self.hole(binder_type.clone())?,
        };
        self.numeric_argument(function, type_)
''')
    path.write_text(text)


if __name__ == '__main__':
    {'tests': tests, 'implementation': implementation}[sys.argv[1]]()
