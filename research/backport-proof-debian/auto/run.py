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
    git('merge', '--no-ff', '--no-edit', res[0]['git_branch'])
    git('worktree', 'remove', '--force', res[0]['worktree'])
    git('branch', '-d', res[0]['git_branch'])
    log.append(f"{f['patch']}: {res[0]['verdict']} {res[0]['reasons']}")
    return True


def run_branch(branch: str, public: Path, work: Path, budget: int, log: list[str]) -> int:
    src = state_file(public, branch)
    state = json.loads(src.read_text()) if src.exists() else {'commit': None, 'patches': {}}
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
        name = branch.removeprefix('prove/')
        dest = work / 'leftover' / f'{name}-{stamp}'
        dest.parent.mkdir(parents=True, exist_ok=True)
        git('worktree', 'move', str(path), str(dest))
        git('branch', '-m', branch, f'leftover/{name}-{stamp}')
        log.append(f'recover: worktree of {branch} moved to {dest}')


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
    try:
        recover(args.work.resolve(), log)
        shutil.rmtree(args.work / 'state', ignore_errors=True)
        budget = args.max_proofs
        for branch in args.branch or BRANCHES:
            budget = run_branch(branch, args.public.resolve(), args.work.resolve(), budget, log)
        pub = [sys.executable, str(HERE.parent / 'publish' / 'publish.py'), str(args.public),
               '--state', str(args.work / 'state'), '--repo', str(REPO)]
        out = subprocess.run(pub + (['--no-push'] if args.no_push else []),
                             capture_output=True, text=True, check=True).stdout.strip()
        log.append(f'publish: {out}')
    finally:
        lock.unlink()
    print('\n'.join(log))
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
