"""Run the shared source matrix against the authenticated Reference, tests only."""
from pathlib import Path
import json
import os
import subprocess
import sys

lean = Path(os.environ['FLN_REFERENCE_LEAN'])
assert subprocess.check_output([str(lean), '--githash'], text=True).strip() == '8c9756b28d64dab099da31a4c09229a9e6a2ef35'
directory = Path(os.environ['RUNNER_TEMP']) / 'empty-matrix-oracle'
directory.mkdir(exist_ok=True)
counts = [0, 0]
for row in Path(sys.argv[1]).read_text().splitlines():
    if not row or row.startswith('#'):
        continue
    identifier, verdict, source = row.split('\t', 2)
    assert verdict in ('accept', 'reject')
    source = 'prelude\nimport Init.Core\n' + source.replace('\\n', '\n') + '\n'
    path = directory / f'{identifier}.lean'
    path.write_text(source)
    result = subprocess.run([str(lean), str(path)], text=True, capture_output=True, timeout=60)
    print(json.dumps({'id': identifier, 'expected': verdict, 'exit': result.returncode,
                      'stdout': result.stdout, 'stderr': result.stderr}), flush=True)
    assert result.returncode in (0, 1), 'a crash is not a semantic refusal'
    assert (result.returncode == 0) == (verdict == 'accept'), identifier
    counts[verdict == 'reject'] += 1
assert counts == [18, 10], counts
print('PIN_EMPTY_MATRIX: 18 accepted and 10 refused; all matched', flush=True)
