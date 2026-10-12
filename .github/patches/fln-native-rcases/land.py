import os
from pathlib import Path
import subprocess
import tempfile

PAYLOAD = Path(__file__).resolve().parent
ROOT = Path.cwd()
ENV = dict(os.environ, CARGO_TARGET_DIR=os.environ['RUNNER_TEMP'] + '/rcases-target')
FILES = ['crates/fln-elab/src/source/tactics.rs', 'crates/fln-elab/src/source/tactics/eliminate.rs', 'crates/fln-elab/src/source/tactics/rcases.rs', 'crates/fln/tests/source_rcases.rs', 'crates/fln/tests/fixtures/rcases.tsv']

def run(args, cwd=ROOT):
    result = subprocess.run(args, cwd=cwd, env=ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = result.stdout
    print('+', ' '.join(args), 'exit', result.returncode, flush=True)
    if result.returncode:
        print(log[-18000:], flush=True)
        raise RuntimeError('command failed')
    for line in log.splitlines():
        if line.startswith(('test ', 'RCASES ', 'PIN_', 'PRODUCTION_', '[detached', 'To https:', '  ', 'create mode')):
            print(line[:400], flush=True)
    return log

for attempt in range(3):
    run(['git', 'fetch', 'origin', 'main'])
    base = run(['git', 'rev-parse', 'FETCH_HEAD']).strip()
    work = Path(tempfile.mkdtemp(prefix='rcases-work-', dir=os.environ['RUNNER_TEMP']))
    run(['git', 'worktree', 'add', '--detach', str(work), base])
    run(['python3', str(PAYLOAD / 'apply.py'), 'tests'], work)
    if attempt == 0:
        result = subprocess.run(['cargo', 'test', '--locked', '-p', 'fln', '--test', 'source_rcases', 'rcases_and_functions_pass_both_checkers', '--', '--exact'], cwd=work, env=ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        print('BASELINE', result.returncode, result.stdout[-5000:], flush=True)
        if result.returncode == 0 or 'UnsupportedTactic' not in result.stdout or 'FAILED' not in result.stdout:
            raise RuntimeError('expected pre-implementation unsupported tactic was not reproduced')
    run(['python3', str(PAYLOAD / 'apply.py'), 'implementation'], work)
    run(['rustfmt', '--edition', '2024', '--config', 'skip_children=true', *[f for f in FILES if f.endswith('.rs')]], work)
    run(['git', 'diff', '--check'], work)
    # The shared fixture is the acceptance boundary, judged independently by the pin.
    lean = os.environ['FLN_REFERENCE_LEAN']
    counts = [0, 0]
    for line in (work / FILES[-1]).read_text().splitlines():
        name, verdict, source = line.split('\t', 2)
        subject = Path(os.environ['RUNNER_TEMP']) / ('rcases-' + name + '.lean')
        subject.write_text('import Init.RCases\n' + source.replace('\\n', '\n') + '\n')
        result = subprocess.run([lean, str(subject)], text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30)
        if (result.returncode == 0) != (verdict == 'accept'):
            raise RuntimeError(f'pin {name} {verdict}: {result.returncode}\n{result.stdout}')
        counts[verdict != 'accept'] += 1
    print('PIN_RCASES', counts, flush=True)
    run(['cargo', 'test', '--locked', '-p', 'fln', '--test', 'source_rcases', '--test', 'source_matching', '--', '--nocapture'], work)
    run(['cargo', 'clippy', '--locked', '-p', 'fln-elab', '--lib', '--', '-D', 'warnings'], work)
    run(['cargo', 'clippy', '--locked', '-p', 'fln', '--test', 'source_rcases', '--no-deps', '--', '-D', 'warnings'], work)
    run(['git', 'add', '--', *FILES], work)
    staged = run(['git', 'diff', '--cached', '--name-only'], work).splitlines()
    if set(staged) != set(FILES):
        raise RuntimeError(f'unexpected staged paths: {staged}')
    run(['git', 'diff', '--cached', '--check'], work)
    run(['git', '-c', 'user.name=ChatGPT', '-c', 'user.email=noreply@openai.com', 'commit', '-m', 'feat(elab): execute recursive case patterns through checked dependent elimination', '-m', 'Native rcases supports nested tuples and alternatives, constructor-field packing, implicit-field skipping, computed subjects and checked type ascriptions. Preserve each live branch and remove eliminated source locals. Tests run on seed and actual admitted Init.RCases, with the same 14 accepted and 9 refused cases judged by the authenticated Reference. Library and target Clippy pass. rfl, clear and multi-target patterns remain explicitly unsupported.', '-m', f'Validated on parent {base}; GitHub Actions run {os.environ["GITHUB_RUN_ID"]}. No new kernel rules or dependencies.'], work)
    result = subprocess.run(['git', 'push', 'origin', 'HEAD:main'], cwd=work, env=ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, flush=True)
    if result.returncode == 0:
        print('PRODUCTION_COMMIT', run(['git', 'rev-parse', 'HEAD'], work).strip(), flush=True)
        break
    if 'non-fast-forward' not in result.stdout and 'fetch first' not in result.stdout:
        raise RuntimeError('push failed for a reason other than concurrent main')
else:
    raise RuntimeError('main advanced during every tested attempt; no force push')
