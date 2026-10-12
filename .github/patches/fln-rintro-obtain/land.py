import os
from pathlib import Path
import subprocess
import tempfile

PAYLOAD = Path(__file__).resolve().parent
ROOT = Path.cwd()
ENV = dict(os.environ, CARGO_TARGET_DIR=os.environ['RUNNER_TEMP'] + '/rintro-target')
FILES = ['crates/fln-elab/src/source/tactics.rs', 'crates/fln-elab/src/source/tactics/rcases.rs', 'crates/fln-elab/src/source/tactics/rcases/derived.rs', 'crates/fln/tests/source_rintro_obtain.rs', 'crates/fln/tests/fixtures/rintro_obtain.tsv']

def run(args, cwd=ROOT):
    print('+', ' '.join(args), flush=True)
    result = subprocess.run(args, cwd=cwd, env=ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=1200)
    print('EXIT', result.returncode, flush=True)
    if result.returncode:
        print(result.stdout[-22000:], flush=True)
        raise RuntimeError('command failed')
    for line in result.stdout.splitlines():
        if line.startswith(('test ', 'RINTRO_OBTAIN ', '[detached', '    Finished')):
            print(line[:500], flush=True)
    return result.stdout

for attempt in range(3):
    run(['git', 'fetch', 'origin', 'main'])
    base = run(['git', 'rev-parse', 'FETCH_HEAD']).strip()
    work = Path(tempfile.mkdtemp(prefix='rintro-work-', dir=os.environ['RUNNER_TEMP']))
    run(['git', 'worktree', 'add', '--detach', str(work), base])
    run(['python3', str(PAYLOAD / 'apply.py'), 'tests'], work)
    seed = ['cargo', 'test', '--locked', '-p', 'fln', '--test', 'source_rintro_obtain', 'recursive_introductions_and_obtained_witnesses_pass_both_checkers', '--', '--exact', '--nocapture']
    if attempt == 0:
        result = subprocess.run(seed, cwd=work, env=ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=300)
        print('BASELINE', result.returncode, result.stdout[-6000:], flush=True)
        if result.returncode == 0 or 'UnsupportedTactic' not in result.stdout or 'FAILED' not in result.stdout or 'rintro_pair' not in result.stdout:
            raise RuntimeError('expected pre-implementation rintro failure was not reproduced')
    run(['python3', str(PAYLOAD / 'apply.py'), 'implementation'], work)
    run(['rustfmt', '--edition', '2024', '--config', 'skip_children=true', *[f for f in FILES if f.endswith('.rs')]], work)
    run(['git', 'diff', '--check'], work)
    counts = [0, 0]
    mismatches = []
    for fixture in ['crates/fln/tests/fixtures/rcases.tsv', FILES[-1]]:
        for line in (work / fixture).read_text().splitlines():
            if not line.strip() or line.startswith('#'): continue
            name, verdict, source = line.split('\t', 2)
            subject = Path(os.environ['RUNNER_TEMP']) / ('rintro-' + name + '.lean')
            subject.write_text('import Init.RCases\n' + source.replace('\\n', '\n') + '\n')
            result = subprocess.run([os.environ['FLN_REFERENCE_LEAN'], str(subject)], text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30)
            if (result.returncode == 0) != (verdict == 'accept'):
                mismatches.append(name)
                print('PIN_MISMATCH', name, verdict, result.returncode, result.stdout, flush=True)
            counts[verdict != 'accept'] += 1
    if mismatches:
        for i, source in enumerate([
            'theorem f (p : Prop) (hp : p) : p := by obtain h : p; trace_state',
            'theorem f (p : Prop) (hp : p) : p := by obtain h : p; exact hp; trace_state',
            'theorem f (p : Prop) (hp : p) : p := by\n  obtain h : p\n  · exact hp\n  trace_state\n  exact h',
            'theorem f (p : Prop) (hp : p) : p := by\n  obtain h : p\n  · exact hp\n  exact hp',
            'theorem f (p : Prop) (hp : p) : p := by obtain : p; exact hp; trace_state',
            'theorem f (p q : Prop) (h : p ∧ q) : q := by obtain ⟨hp, hq⟩ : p ∧ q; exact h; trace_state',
        ]):
            subject = Path(os.environ['RUNNER_TEMP']) / f'obtain-scope-{i}.lean'
            subject.write_text('import Init.RCases\n' + source + '\n')
            result = subprocess.run([os.environ['FLN_REFERENCE_LEAN'], str(subject)], text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30)
            print('SCOPE_PROBE', i, repr(source), result.returncode, result.stdout, flush=True)
        raise RuntimeError(f'Reference acceptance mismatch; no production activation: {mismatches}')
    if counts != [36, 23]: raise RuntimeError(f'unexpected oracle counts: {counts}')
    print('PIN_RINTRO_OBTAIN', counts, flush=True)
    run(seed, work)
    run(['cargo', 'clippy', '--locked', '-p', 'fln-elab', '--lib', '--', '-D', 'warnings'], work)
    run(['cargo', 'clippy', '--locked', '-p', 'fln', '--test', 'source_rintro_obtain', '--no-deps', '--', '-D', 'warnings'], work)
    run(['cargo', 'test', '--locked', '-p', 'fln', '--test', 'source_rintro_obtain', 'actual_imported_rcases_checks_introductions_and_obtained_witnesses', '--', '--exact', '--nocapture'], work)
    run(['cargo', 'test', '--locked', '-p', 'fln', '--test', 'source_matching'], work)
    run(['git', 'add', '--', *FILES], work)
    staged = run(['git', 'diff', '--cached', '--name-only'], work).splitlines()
    if set(staged) != set(FILES): raise RuntimeError(f'unexpected staged paths: {staged}')
    run(['git', 'diff', '--cached', '--check'], work)
    run(['git', '-c', 'user.name=ChatGPT', '-c', 'user.email=noreply@openai.com', 'commit', '-m', 'feat(elab): execute recursive introductions and obtained witness proofs', '-m', 'Implement rintro nested patterns, dependent introductions and nearest type annotations using the checked rcases backend. Implement obtain with supplied values or separately checked witness goals; newly assumed witnesses remain out of scope in their own proof obligation. Preserve every live branch and refusal atomicity. The combined 59-case matrix (36 accepted, 23 refused) passes natively, with actual admitted Init.RCases, and at the authenticated Reference. This includes all 27 rcases controls from 927c0d94, whose earlier commit message omitted the four default-pattern controls. All 34 source_matching tests and strict library/target Clippy pass.', '-m', f'Validated on parent {base}; GitHub Actions run {os.environ["GITHUB_RUN_ID"]}. No kernel rules or dependencies added.'], work)
    result = subprocess.run(['git', 'push', 'origin', 'HEAD:main'], cwd=work, env=ENV, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, flush=True)
    if result.returncode == 0:
        print('PRODUCTION_COMMIT', run(['git', 'rev-parse', 'HEAD'], work).strip(), flush=True)
        break
    if 'non-fast-forward' not in result.stdout and 'fetch first' not in result.stdout:
        raise RuntimeError('push failed for a reason other than concurrent main')
else:
    raise RuntimeError('main advanced during every tested attempt; no force push')
