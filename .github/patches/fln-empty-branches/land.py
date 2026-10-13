"""Validate native empty-branch elimination, then fast-forward main only."""
from pathlib import Path
import json
import os
import subprocess

PAYLOAD = Path(__file__).resolve().parent
REPO = Path.cwd()
TEMP = Path(os.environ['RUNNER_TEMP'])
ENV = dict(os.environ, CARGO_TARGET_DIR=str(TEMP / 'empty-branches-target'))
FILES = ['crates/fln-elab/src/source/tactics/empty.rs',
         'crates/fln-elab/src/source/tactics/eliminate.rs',
         'crates/fln-elab/src/source/tactics/constructors.rs',
         'crates/fln/tests/source_empty_branches.rs',
         'crates/fln/tests/fixtures/empty_branches.tsv']


def run(*args, cwd=REPO, capture=False, check=True):
    print('+', ' '.join(map(str, args)), flush=True)
    return subprocess.run(list(map(str, args)), cwd=cwd, env=ENV, check=check,
                          text=True, stdout=subprocess.PIPE if capture else None,
                          stderr=subprocess.STDOUT if capture else None)


def inspect_beads(work):
    beads = [json.loads(line) for line in (work / '.beads/issues.jsonl').read_text().splitlines() if line]
    active = [b for b in beads if b.get('status') in ('open', 'in_progress')]
    active.sort(key=lambda b: (b.get('priority', 9), b.get('id', '')))
    for bead in active[:60]:
        print('BEAD_OPEN', json.dumps({key: bead.get(key) for key in ('id', 'title', 'priority', 'status')}, ensure_ascii=False), flush=True)
    for bead in beads:
        if bead['id'] == 'fln-nomatch-nofun-h78u':
            print('BEAD_TARGET', json.dumps({key: bead.get(key) for key in ('id', 'title', 'status', 'description', 'notes')}, ensure_ascii=False), flush=True)


def reference(fixture):
    lean = ENV['FLN_REFERENCE_LEAN']
    version = run(lean, '--githash', capture=True).stdout.strip()
    assert version == '8c9756b28d64dab099da31a4c09229a9e6a2ef35', version
    directory = TEMP / 'empty-branches-reference'
    directory.mkdir(exist_ok=True)
    for line in fixture.read_text().splitlines():
        if not line or line.startswith('#'):
            continue
        name, expected, source = line.split('\t', 2)
        path = directory / (name + '.lean')
        path.write_text('prelude\nimport Init.Core\n' + source.replace('\\n', '\n') + '\n')
        result = subprocess.run([lean, str(path)], text=True, capture_output=True, timeout=30)
        print('PIN_EMPTY_BRANCH', json.dumps(dict(id=name, expected=expected, exit=result.returncode,
                                                stdout=result.stdout, stderr=result.stderr)), flush=True)
        assert (result.returncode == 0) == (expected == 'accept'), name


def publish():
    for attempt in range(3):
        run('git', 'fetch', 'origin', 'main')
        base = run('git', 'rev-parse', 'FETCH_HEAD', capture=True).stdout.strip()
        work = TEMP / f'empty-branches-{attempt}'
        run('git', 'worktree', 'add', '--detach', work, base)
        if 'fn empty_field_names(' in (work / FILES[0]).read_text():
            print('empty-field implementation already present; leaving it unchanged', flush=True)
            return
        if attempt == 0:
            inspect_beads(work)
            reference(PAYLOAD / 'cases.tsv')
        run('python3', PAYLOAD / 'apply.py', 'tests', cwd=work)
        before = run('cargo', 'test', '--locked', '-p', 'fln', '--test', 'source_empty_branches',
                     'empty_branches_and_functions_pass_both_checkers', '--', '--exact', '--nocapture',
                     cwd=work, capture=True, check=False)
        print(before.stdout, flush=True)
        assert before.returncode != 0 and 'running 1 test' in before.stdout
        assert 'empty_branches_and_functions_pass_both_checkers ... FAILED' in before.stdout
        run('python3', PAYLOAD / 'apply.py', 'implementation', cwd=work)
        rust = [path for path in FILES if path.endswith('.rs')]
        run('rustfmt', '--edition', '2024', '--config', 'skip_children=true', *rust, cwd=work)
        run('git', 'diff', '--check', cwd=work)
        targets = ['--test', 'source_nomatch', '--test', 'source_empty_matrices', '--test', 'source_empty_branches']
        run('cargo', 'test', '--locked', '-p', 'fln', *targets, '--', '--nocapture', cwd=work)
        run('cargo', 'clippy', '--locked', '-p', 'fln', *targets, '--no-deps', '--', '-D', 'warnings', cwd=work)
        run('cargo', 'clippy', '--locked', '-p', 'fln-elab', '--lib', '--', '-D', 'warnings', cwd=work)
        run('git', 'add', '--', *FILES, cwd=work)
        changed = run('git', 'diff', '--cached', '--name-only', cwd=work, capture=True).stdout.splitlines()
        assert set(changed) == set(FILES), changed
        run('git', 'diff', '--cached', '--check', cwd=work)
        run('git', '-c', 'user.name=ChatGPT', '-c', 'user.email=noreply@openai.com',
            'commit', '-m', 'feat(elab): eliminate impossible constructor fields through checked False proofs',
            '-m', 'Expand nonrecursive empty-matrix fields, preserve dependent field identities and '
                  'roll back live recursive splits while retaining their heartbeat cost. Prove False '
                  'before eliminating proof-valued families into data; no kernel rule or new axiom.',
            '-m', f'Validated on {base} in GitHub Actions run {ENV["GITHUB_RUN_ID"]}: '
                  '19 accepted and 12 refused field cases agree with the authenticated Reference '
                  'and run through both checkers on the seed and actual Init.Core. Existing '
                  'nomatch/matrix regressions and strict library/target Clippy pass.', cwd=work)
        pushed = run('git', 'push', 'origin', 'HEAD:main', cwd=work, check=False)
        if pushed.returncode == 0:
            run('git', 'rev-parse', 'HEAD', cwd=work)
            return
        latest = run('git', 'ls-remote', 'origin', 'refs/heads/main', capture=True).stdout.split()[0]
        if latest == base:
            raise RuntimeError('push failed without a concurrent main update')
        print('Main advanced; reapply and retest a new snapshot without changing history.', flush=True)
    raise RuntimeError('Main remained busy; no history rewrite attempted')


publish()
