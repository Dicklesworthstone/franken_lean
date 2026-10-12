"""Reproduce the P0 numeral false accept, validate its fix, fast-forward main."""
from pathlib import Path
import json
import os
import subprocess

PAYLOAD = Path(__file__).resolve().parent
REPO = Path.cwd()
TEMP = Path(os.environ['RUNNER_TEMP'])
ENV = dict(os.environ, CARGO_TARGET_DIR=str(TEMP / 'numeric-transparency-target'))
FILES = ['crates/fln-elab/src/source/numeric.rs',
         'crates/fln/tests/source_numeric_transparency.rs',
         'crates/fln/tests/fixtures/numeric_transparency.tsv']


def run(*args, cwd=REPO, capture=False, check=True):
    print('+', ' '.join(map(str, args)), flush=True)
    return subprocess.run(list(map(str, args)), cwd=cwd, env=ENV, check=check,
                          text=True, stdout=subprocess.PIPE if capture else None,
                          stderr=subprocess.STDOUT if capture else None)


def reference():
    lean = ENV['FLN_REFERENCE_LEAN']
    assert run(lean, '--githash', capture=True).stdout.strip() == '8c9756b28d64dab099da31a4c09229a9e6a2ef35'
    directory = TEMP / 'numeric-transparency-reference'
    directory.mkdir(exist_ok=True)
    for line in (PAYLOAD / 'cases.tsv').read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        name, expected, source = line.split('\t', 2)
        path = directory / (name + '.lean')
        path.write_text('prelude\nimport Init.Core\n' + source.replace('\\n', '\n') + '\n')
        result = subprocess.run([lean, str(path)], text=True, capture_output=True, timeout=30)
        print('PIN_NUMERIC_TRANSPARENCY', json.dumps(dict(id=name, expected=expected,
              exit=result.returncode, stdout=result.stdout, stderr=result.stderr)), flush=True)
        assert (result.returncode == 0) == (expected == 'accept'), name


reference()
for attempt in range(3):
    run('git', 'fetch', 'origin', 'main')
    base = run('git', 'rev-parse', 'FETCH_HEAD', capture=True).stdout.strip()
    work = TEMP / f'numeric-transparency-{attempt}'
    run('git', 'worktree', 'add', '--detach', work, base)
    for line in (work / '.beads/issues.jsonl').read_text().splitlines():
        record = json.loads(line)
        if record.get('id') == 'fln-5efd':
            print('BEAD_TARGET', json.dumps(record, ensure_ascii=False), flush=True)
    if "Keep the expected type's original head" in (work / FILES[0]).read_text():
        print('Numeric expected-type preservation already present; leaving it unchanged.', flush=True)
        break
    run('python3', PAYLOAD / 'apply.py', 'tests', cwd=work)
    before = run('cargo', 'test', '--locked', '-p', 'fln', '--test', 'source_numeric_transparency',
                 'numeric_transparency_and_functions_pass_both_checkers', '--', '--exact', '--nocapture',
                 cwd=work, capture=True, check=False)
    print(before.stdout, flush=True)
    assert before.returncode != 0 and 'running 1 test' in before.stdout
    assert 'projected_def_zero: incorrectly accepted' in before.stdout
    run('python3', PAYLOAD / 'apply.py', 'implementation', cwd=work)
    run('rustfmt', '--edition', '2024', '--config', 'skip_children=true',
        *[path for path in FILES if path.endswith('.rs')], cwd=work)
    run('git', 'diff', '--check', cwd=work)
    targets = ['--test', 'source_numeric_transparency', '--test', 'source_default_instances',
               '--test', 'source_instance_universe_holes', '--test', 'source_scoped_instance_commands']
    run('cargo', 'test', '--locked', '-p', 'fln', *targets, '--no-fail-fast', '--', '--nocapture', cwd=work)
    run('cargo', 'test', '--locked', '-p', 'fln-elab', '--lib', 'source::numeric::tests', cwd=work)
    run('cargo', 'clippy', '--locked', '-p', 'fln', '--test', 'source_numeric_transparency',
        '--no-deps', '--', '-D', 'warnings', cwd=work)
    run('cargo', 'clippy', '--locked', '-p', 'fln-elab', '--lib', '--', '-D', 'warnings', cwd=work)
    run('git', 'add', '--', *FILES, cwd=work)
    changed = run('git', 'diff', '--cached', '--name-only', cwd=work, capture=True).stdout.splitlines()
    assert set(changed) == set(FILES), changed
    run('git', 'diff', '--cached', '--check', cwd=work)
    run('git', '-c', 'user.name=ChatGPT', '-c', 'user.email=noreply@openai.com',
        'commit', '-m', 'fix(elab): preserve numeric expected types at instance transparency',
        '-m', 'Do not normalize projected semireducible expected types by assigning a fresh '
              'conversion hole before building numeric class obligations. Preserve their checked '
              'type expression while numeric_argument checks the universe. Keep absent-type '
              'inference, reducible projections and explicitly supplied dictionaries working.',
        '-m', f'P0 fln-5efd reproduced as an incorrect acceptance on parent {base}; '
              f'validated in GitHub Actions run {ENV["GITHUB_RUN_ID"]}. Eight accepted and six '
              'refused cases match the authenticated live Reference and both native checking '
              'engines with actual Init.Core. Default/scoped instances, universe holes, numeric '
              'component tests and strict Clippy pass. No new kernel rule, axiom or dependency.', cwd=work)
    pushed = run('git', 'push', 'origin', 'HEAD:main', cwd=work, check=False)
    if pushed.returncode == 0:
        run('git', 'rev-parse', 'HEAD', cwd=work)
        break
    latest = run('git', 'ls-remote', 'origin', 'refs/heads/main', capture=True).stdout.split()[0]
    if latest == base:
        raise RuntimeError('push failed without concurrent main advancement')
    print('Main advanced; reapply and retest a fresh snapshot without altering history.', flush=True)
else:
    raise RuntimeError('Main remained busy; no history rewrite attempted')
