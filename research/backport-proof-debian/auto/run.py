"""One unattended pass of the whole pipeline (PROTOCOL-auto.md §2-§5).

For each Debian branch:
  detect.py --dry-run | mechanism.py --judge   findings with the §3.1/3.2/3.4 verdicts
  a finding with a verdict                     -> case record cases/<release>/<patch>.json
  an open finding (at most --max-proofs)       -> build.py, then prove.py; the proof branch
                                                  is merged here and its worktree removed
Only findings handled in this pass are added to the state, so an open finding left over
by --max-proofs is found again next time. Finally publish.py pushes the copy, the state
and the verdict index. Run it from a checkout that nobody else works in (it commits and
merges on the checked-out branch). A lock file keeps two passes from overlapping.

A pass that was cut off (power off, killed) must not stop every later pass, so a new pass
first clears what it left (`recover`), keeping all of it: a lock whose process is gone is
replaced, uncommitted changes go to `git stash`, and a leftover proof worktree is moved to
<work>/leftover/ with its branch renamed leftover/…, which frees the names prove.py needs.

Usage:
    python3 run.py --public <clone> --work <dir> [--branch debian/trixie ...]
                   [--max-proofs 1] [--no-push]
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
CASES = 'research/backport-proof-debian/cases'
BRANCHES = ('debian/trixie', 'debian/bookworm')
CO_AUTHOR = 'Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>'
MAX_INTERRUPTS = 3


def git(*args: str) -> str:
    proc = subprocess.run(['git', '-C', str(REPO), *args], capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(f'git {" ".join(args)}: {proc.stderr.strip()}')
    return proc.stdout


def commit(paths: list[str], message: str) -> None:
    """Commit the records if they changed; a rerun often rewrites the same verdict."""
    git('add', '--', *paths)
    if subprocess.run(['git', '-C', str(REPO), 'diff', '--cached', '--quiet']).returncode:
        git('commit', '-q', '-m', f'{message}\n\n{CO_AUTHOR}')


def tool(name: str, *args: str, stdin: str = '', cwd: Path = HERE) -> list[dict]:
    proc = subprocess.run([sys.executable, str(HERE / name), *args], input=stdin, cwd=cwd,
                          capture_output=True, text=True)
    if proc.returncode not in (0, 1):
        raise RuntimeError(f'{name} exit {proc.returncode}: {proc.stderr.strip()[-1500:]}')
    try:  # prove.py prints one indented document; the others print JSON lines
        return [json.loads(proc.stdout)]
    except json.JSONDecodeError:
        return [json.loads(line) for line in proc.stdout.splitlines() if line.startswith('{')]


def state_file(public: Path, branch: str) -> Path:
    return public / 'state' / (branch.replace('/', '-') + '.json')


def record_for(f: dict) -> dict:
    """§3.7 record for a finding the rules decided before any proof."""
    keep = ('c_files', 'changed_lines', 'up_in_deb', 'deb_added', 'up_added')
    return {'patch': f['patch'], 'cve': f['cve'], 'branch': f['branch'],
            'debian_commit': f['commit'], 'upstream_fixed': f.get('upstream_fixed'),
            'verdict': f['verdict'], 'detail': f.get('detail', ''), 'scope': None,
            'property_changed': None, 'external_specs': {}, 'lean_modules': [],
            'theorems': {}, 'd_functions': {}, **{k: f[k] for k in keep if k in f}}


def write_record(f: dict) -> str:
    release = f['branch'].split('/')[-1]
    rel = f"{CASES}/{release}/{f['patch'].removesuffix('.patch')}.json"
    path = REPO / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(record_for(f), ensure_ascii=False, indent=1) + '\n')
    return rel


def interrupted(rec: dict) -> bool:
    """A proof job that stopped by itself before its time limit (the API connection was lost while
    the Mac slept, a crash): its 「証明できず」 says nothing about the patch, so it is not a verdict."""
    return rec.get('claude_exit') not in (0, None) and not rec.get('timed_out')


def retries_left(work: Path, name: str) -> bool:
    """An interrupted job is retried by the next pass; the third interruption is kept as the verdict."""
    shelved = work / 'leftover'
    return not shelved.exists() or sum(
        1 for p in shelved.iterdir() if p.name.rsplit('-', 1)[0] == name) < MAX_INTERRUPTS - 1


def retry_interrupted(branch: str, patches: dict, work: Path, log: list[str]) -> dict:
    """Drop from the state the patches whose published verdict came from an interrupted job,
    unless that job was already the last try (`retries_left`)."""
    release = branch.split('/')[-1]
    kept = {}
    for patch, sha in patches.items():
        stem = patch.removesuffix('.patch')
        path = REPO / CASES / release / (stem + '.prove.json')
        if (path.exists() and interrupted(json.loads(path.read_text()))
                and retries_left(work, f'{release}-{stem}')):
            log.append(f'{patch}: the published verdict came from an interrupted job; proved again')
            continue
        kept[patch] = sha
    return kept


def shelve(path: Path, branch: str, work: Path, log: list[str]) -> None:
    """Move a proof worktree to <work>/leftover/ and rename its branch, keeping all of it."""
    name = branch.removeprefix('prove/')
    dest = work / 'leftover' / f'{name}-{time.strftime("%Y%m%dT%H%M%S")}'
    dest.parent.mkdir(parents=True, exist_ok=True)
    git('worktree', 'move', str(path), str(dest))
    git('branch', '-m', branch, f'leftover/{dest.name}')
    log.append(f'worktree of {branch} moved to {dest}')


def prove_one(f: dict, out: Path, log: list[str]) -> bool:
    """build.py and prove.py for one open finding; True when it reached a verdict."""
    built = tool('build.py', str(out), stdin=json.dumps(f) + '\n')
    if not built or 'error' in built[0]:
        log.append(f"{f['patch']}: build.py failed: {built}")
        return False
    if built[0]['verdict'] is not None:
        commit([write_record({**f, 'verdict': built[0]['verdict']})],
               f"docs: {f['patch']} ({f['branch']}): {built[0]['verdict']}")
        return True
    case_dir = out / f['patch'].removesuffix('.patch')
    res = tool('prove.py', str(case_dir), '--repo', str(REPO))
    if not res:
        log.append(f"{f['patch']}: prove.py gave no result")
        return False
    name = res[0]['git_branch'].removeprefix('prove/')
    if interrupted(res[0]) and retries_left(out.parent, name):
        log.append(f"{f['patch']}: the job was interrupted (exit {res[0]['claude_exit']}); retried next pass")
        shelve(Path(res[0]['worktree']), res[0]['git_branch'], out.parent, log)
        return False
    git('merge', '--no-ff', '--no-edit', res[0]['git_branch'])
    git('worktree', 'remove', '--force', res[0]['worktree'])
    git('branch', '-d', res[0]['git_branch'])
    log.append(f"{f['patch']}: {res[0]['verdict']} {res[0]['reasons']}")
    return True


def run_branch(branch: str, public: Path, work: Path, budget: int, log: list[str]) -> int:
    src = state_file(public, branch)
    state = json.loads(src.read_text()) if src.exists() else {'commit': None, 'patches': {}}
    state = {**state, 'patches': retry_interrupted(branch, state['patches'], work, log)}
    tmp = work / 'detect-state.json'
    tmp.write_text(json.dumps(state))
    found = tool('detect.py', branch, str(tmp), '--dry-run')
    judged = tool('mechanism.py', '--judge', stdin=''.join(json.dumps(f) + '\n' for f in found))
    decided = [f for f in judged if f.get('verdict') is not None]
    seen = dict(state['patches'])
    if decided:
        commit([write_record(f) for f in decided], f'docs: {len(decided)} verdicts decided by rule ({branch})')
        seen.update({f['patch']: f['sha256'] for f in decided})
    for f in (f for f in judged if f.get('verdict') is None):
        if budget <= 0:
            log.append(f"{f['patch']}: left for a later pass (--max-proofs)")
            continue
        budget -= 1
        if prove_one(f, work / ('out-' + branch.split('/')[-1]), log):
            seen[f['patch']] = f['sha256']
    head = judged[0]['commit'] if judged else state.get('commit')
    out = work / 'state' / src.name
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({'commit': head, 'patches': seen}, indent=1) + '\n')
    return budget


def pid_alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def take_lock(lock: Path, log: list[str]) -> bool:
    """Create the lock; replace it when the pass that wrote it is no longer running."""
    for _ in range(2):
        try:
            fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
        except FileExistsError:
            text = lock.read_text().strip()
            if text.isdigit() and pid_alive(int(text)):
                return False
            log.append(f'recover: {lock.name} of pid {text or "?"} was left by a pass that is gone; replaced')
            lock.unlink(missing_ok=True)
            continue
        os.write(fd, str(os.getpid()).encode())
        os.close(fd)
        return True
    return False


def prove_worktrees() -> list[tuple[Path, str]]:
    """(path, branch) of every worktree on a prove/ branch; a finished proof removes its own."""
    out, path = [], None
    for line in git('worktree', 'list', '--porcelain').splitlines():
        if line.startswith('worktree '):
            path = Path(line.removeprefix('worktree '))
        elif line.startswith('branch refs/heads/prove/') and path is not None:
            out.append((path, line.removeprefix('branch refs/heads/')))
    return out


def recover(work: Path, log: list[str]) -> None:
    stamp = time.strftime('%Y%m%dT%H%M%S')
    if git('status', '--porcelain', '--untracked-files=no').strip():
        git('stash', 'push', '-m', f'leftover {stamp}: uncommitted changes of an interrupted pass')
        log.append(f'recover: uncommitted changes stashed (leftover {stamp})')
    for path, branch in prove_worktrees():
        shelve(path, branch, work, log)
        log[-1] = f'recover: {log[-1]}'


def last_run(started: str, finished: str, log: list[str], error: BaseException | None) -> dict:
    """state/last-run.json: what a reader outside this machine needs to tell a pass that failed
    from one that had nothing to do. The file is public, so the home directory is not shown."""
    home = str(Path.home())
    err = None if error is None else f'{type(error).__name__}: {error}'[-1500:]
    return {'started': started, 'finished': finished, 'ok': error is None,
            'error': err and err.replace(home, '~'), 'log': [line.replace(home, '~') for line in log]}


def report_failure(public: Path, rec: dict, push: bool) -> None:
    """Commit only the report: a pass that failed inside publish may have left the clone half-written."""
    rel = 'state/last-run.json'
    (public / 'state').mkdir(exist_ok=True)
    (public / rel).write_text(json.dumps(rec, ensure_ascii=False, indent=1) + '\n')
    for args in (['add', '--', rel], ['commit', '-q', '-m', f'state: the last pass failed\n\n{CO_AUTHOR}', '--', rel]):
        subprocess.run(['git', '-C', str(public), *args], check=True, capture_output=True)
    if push:
        branch = subprocess.run(['git', '-C', str(public), 'symbolic-ref', '--short', 'HEAD'], check=True,
                                capture_output=True, text=True).stdout.strip()
        subprocess.run(['git', '-C', str(public), 'push', '-q', 'origin', branch], check=True, capture_output=True)


def stamp() -> str:
    return time.strftime('%Y-%m-%dT%H:%M:%S%z')


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--public', type=Path, required=True)
    ap.add_argument('--work', type=Path, required=True)
    ap.add_argument('--branch', action='append')
    ap.add_argument('--max-proofs', type=int, default=1)
    ap.add_argument('--no-push', action='store_true')
    args = ap.parse_args(argv)
    args.work.mkdir(parents=True, exist_ok=True)
    lock = args.work / 'run.lock'
    log: list[str] = []
    if not take_lock(lock, log):
        print(f'{lock} exists: another pass is running', file=sys.stderr)
        return 2
    started = stamp()
    try:
        recover(args.work.resolve(), log)
        shutil.rmtree(args.work / 'state', ignore_errors=True)
        budget = args.max_proofs
        for branch in args.branch or BRANCHES:
            budget = run_branch(branch, args.public.resolve(), args.work.resolve(), budget, log)
        # finished is the time publish starts: the report travels in the same commit
        (args.work / 'state' / 'last-run.json').write_text(
            json.dumps(last_run(started, stamp(), log, None), ensure_ascii=False, indent=1) + '\n')
        pub = [sys.executable, str(HERE.parent / 'publish' / 'publish.py'), str(args.public),
               '--state', str(args.work / 'state'), '--repo', str(REPO)]
        out = subprocess.run(pub + (['--no-push'] if args.no_push else []),
                             capture_output=True, text=True, check=True).stdout.strip()
        log.append(f'publish: {out}')
    except Exception as e:
        if isinstance(e, subprocess.CalledProcessError):
            e = RuntimeError(f'{e} {(e.stderr or "").strip()[-1000:]}')
        print('\n'.join(log))
        report_failure(args.public.resolve(), last_run(started, stamp(), log, e), not args.no_push)
        raise
    finally:
        lock.unlink()
    print('\n'.join(log))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
