"""Test implementation in fresh main snapshots and publish normal fast-forwards.

Each retry creates a new detached worktree. It never resets, deletes, rebases,
force-pushes, or replaces another author's files. Existing worktrees stay intact.
"""
from pathlib import Path
import os
import subprocess

PAYLOAD = Path(__file__).resolve().parent
REPOSITORY = Path.cwd()
TEMP = Path(os.environ['RUNNER_TEMP'])
ENV = dict(os.environ, CARGO_TARGET_DIR=str(TEMP / 'empty-matrix-target'))
SINGLE = ['crates/fln-elab/src/source.rs', 'crates/fln-elab/src/source/matching.rs',
          'crates/fln-elab/src/source/matching/nomatch.rs', 'crates/fln/tests/source_nomatch.rs']
MATRIX = ['crates/fln-elab/src/source.rs', 'crates/fln-elab/src/source/tactics.rs',
          'crates/fln-elab/src/source/tactics/eliminate.rs',
          'crates/fln-elab/src/source/tactics/empty.rs',
          'crates/fln-elab/src/source/matching/nomatch.rs',
          'crates/fln/tests/source_nomatch.rs', 'crates/fln/tests/source_empty_matrices.rs',
          'crates/fln/tests/fixtures/empty_matrices.tsv']


def run(*args, cwd=REPOSITORY, capture=False, check=True):
    print('+', ' '.join(map(str, args)), flush=True)
    return subprocess.run(list(map(str, args)), cwd=cwd, env=ENV, check=check,
                          text=True, stdout=subprocess.PIPE if capture else None)


def publish(phase):
    files = SINGLE if phase == 'single' else MATRIX
    for attempt in range(3):
        run('git', 'fetch', 'origin', 'main')
        base = run('git', 'rev-parse', 'FETCH_HEAD', capture=True).stdout.strip()
        work = TEMP / f'empty-{phase}-{attempt}'
        run('git', 'worktree', 'add', '--detach', work, base)
        marker = work / ('crates/fln-elab/src/source/matching/nomatch.rs' if phase == 'single'
                         else 'crates/fln-elab/src/source/tactics/empty.rs')
        if marker.exists():
            print(f'{phase} already exists on main; leaving its files unchanged', flush=True)
            return
        if phase == 'single':
            script = REPOSITORY / '.github/patches/fln-empty-matches/apply.py'
            run('python3', script, 'tests', cwd=work)
            run('python3', script, 'implementation', cwd=work)
            targets = ['--test', 'source_nomatch']
        else:
            run('python3', PAYLOAD / 'apply.py', cwd=work)
            targets = ['--test', 'source_nomatch', '--test', 'source_empty_matrices']
        rust = [file for file in files if file.endswith('.rs')]
        run('rustfmt', '--edition', '2024', '--config', 'skip_children=true', *rust, cwd=work)
        run('git', 'diff', '--check', cwd=work)
        run('cargo', 'test', '--locked', '-p', 'fln', *targets, '--', '--nocapture', cwd=work)
        run('cargo', 'clippy', '--locked', '-p', 'fln', *targets, '--no-deps', '--', '-D', 'warnings', cwd=work)
        run('cargo', 'clippy', '--locked', '-p', 'fln-elab', '--lib', '--', '-D', 'warnings', cwd=work)
        if phase == 'matrix':
            run('python3', PAYLOAD / 'oracle.py', work / 'crates/fln/tests/fixtures/empty_matrices.tsv', cwd=work)
        run('git', 'add', '--', *files, cwd=work)
        changed = run('git', 'diff', '--cached', '--name-only', capture=True, cwd=work).stdout.splitlines()
        assert set(changed) == set(files), f'unexpected staged paths: {changed}'
        run('git', 'diff', '--cached', '--check', cwd=work)
        message = ('feat(elab): elaborate empty matches through checked case equations' if phase == 'single'
                   else 'feat(elab): elaborate nofun and dependent empty pattern matrices')
        evidence = ('Seven source_nomatch integration tests and strict target/library Clippy pass. '
                    'The positive regression was independently reproduced on the unmodified source in run 38223664706.'
                    if phase == 'single' else
                    'Single-column regressions plus shared positive/refusal matrices pass on the seed and actual '
                    'admitted Init.Core artifacts. The same matrix matches the authenticated live Reference. '
                    'Strict target/library Clippy passes.')
        run('git', '-c', 'user.name=ChatGPT', '-c', 'user.email=noreply@openai.com',
            'commit', '-m', message, '-m', evidence,
            '-m', f'Validated on parent {base}; GitHub Actions run {os.environ["GITHUB_RUN_ID"]}. '
                  'No kernel rule, axiom, dependency or ordinary-match coverage relaxation.', cwd=work)
        result = run('git', 'push', 'origin', 'HEAD:main', cwd=work, check=False)
        if result.returncode == 0:
            run('git', 'rev-parse', 'HEAD', cwd=work)
            return
        latest = run('git', 'ls-remote', 'origin', 'refs/heads/main', capture=True).stdout.split()[0]
        if latest == base:
            raise RuntimeError('publication failed without a concurrent head change')
        print('main advanced: reapply and revalidate in another new worktree', flush=True)
    raise RuntimeError('main remained busy; no force-push was attempted')


publish('single')
publish('matrix')
