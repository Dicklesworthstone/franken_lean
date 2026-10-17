"""Land constructor expansion first, then selected-evidence contradiction leaves."""
from pathlib import Path
import os
import runpy

PAYLOAD = Path(__file__).resolve().parent
TEMP = Path(os.environ['RUNNER_TEMP'])
# The existing landing function validates and publishes the first feature on a
# fresh main snapshot. Reuse only its command/oracle helpers after it finishes.
previous = runpy.run_path(str(PAYLOAD.parent / 'fln-empty-branches/land.py'))
run = previous['run']
reference = previous['reference']
FILES = ['crates/fln-elab/src/source/tactics/empty.rs',
         'crates/fln-elab/src/source/tactics/constructors.rs',
         'crates/fln/tests/source_empty_contradictions.rs',
         'crates/fln/tests/fixtures/empty_contradictions.tsv']

reference(PAYLOAD / 'cases.tsv')
for attempt in range(3):
    run('git', 'fetch', 'origin', 'main')
    base = run('git', 'rev-parse', 'FETCH_HEAD', capture=True).stdout.strip()
    work = TEMP / f'empty-contradictions-{attempt}'
    run('git', 'worktree', 'add', '--detach', work, base)
    if 'self.contradict_evidence_goal(goal, selected)' in (work / FILES[0]).read_text():
        print('Selected-evidence leaves already present; leaving them unchanged.', flush=True)
        break
    run('python3', PAYLOAD / 'apply.py', 'tests', cwd=work)
    before = run('cargo', 'test', '--locked', '-p', 'fln', '--test', 'source_empty_contradictions',
                 'empty_contradictions_and_functions_pass_both_checkers', '--', '--exact', '--nocapture',
                 cwd=work, capture=True, check=False)
    print(before.stdout, flush=True)
    assert before.returncode != 0 and 'running 1 test' in before.stdout
    assert 'empty_contradictions_and_functions_pass_both_checkers ... FAILED' in before.stdout
    run('python3', PAYLOAD / 'apply.py', 'implementation', cwd=work)
    run('rustfmt', '--edition', '2024', '--config', 'skip_children=true',
        *[path for path in FILES if path.endswith('.rs')], cwd=work)
    run('git', 'diff', '--check', cwd=work)
    targets = ['--test', 'source_nomatch', '--test', 'source_empty_matrices',
               '--test', 'source_empty_branches', '--test', 'source_empty_contradictions']
    run('cargo', 'test', '--locked', '-p', 'fln', *targets, '--', '--nocapture', cwd=work)
    run('cargo', 'clippy', '--locked', '-p', 'fln', *targets, '--no-deps', '--', '-D', 'warnings', cwd=work)
    run('cargo', 'clippy', '--locked', '-p', 'fln-elab', '--lib', '--', '-D', 'warnings', cwd=work)
    run('git', 'add', '--', *FILES, cwd=work)
    changed = run('git', 'diff', '--cached', '--name-only', cwd=work, capture=True).stdout.splitlines()
    assert set(changed) == set(FILES), changed
    run('git', 'diff', '--cached', '--check', cwd=work)
    run('git', '-c', 'user.name=ChatGPT', '-c', 'user.email=noreply@openai.com',
        'commit', '-m', 'feat(elab): close empty matrices with scoped contradiction evidence',
        '-m', 'Track selected discriminants and exposed fields through branch specialization. '
              'Close terminal False goals with ordinary contradiction proofs without capturing '
              'unrelated ambient hypotheses. Preserve normal contradiction tactic evidence.',
        '-m', f'Validated on {base} in GitHub Actions run {os.environ["GITHUB_RUN_ID"]}: '
              '16 accepted and 10 refused cases match the authenticated Reference and both '
              'checking engines on the native seed and actual Init.Core. All prior empty-match '
              'and field regressions and strict target/library Clippy pass.', cwd=work)
    pushed = run('git', 'push', 'origin', 'HEAD:main', cwd=work, check=False)
    if pushed.returncode == 0:
        run('git', 'rev-parse', 'HEAD', cwd=work)
        break
    latest = run('git', 'ls-remote', 'origin', 'refs/heads/main', capture=True).stdout.split()[0]
    if latest == base:
        raise RuntimeError('push failed without concurrent advancement')
    print('Main advanced: repeat validation on a fresh snapshot, never force-push.', flush=True)
else:
    raise RuntimeError('Main remained busy; no history rewrite attempted')
