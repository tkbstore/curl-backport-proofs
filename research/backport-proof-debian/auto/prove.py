"""Run one proof job (PROTOCOL-auto.md §3.5-3.6) and decide its verdict.

Takes one case directory written by build.py (<out>/<patch name without .patch>/,
with manifest.json). For an open case it:
  1. adds a git worktree <repo>-prove-<release>-<stem> on branch prove/<release>-<stem>
     off the current HEAD, copies the lake cache, and commits the build.py inputs
     under research/c-semantics-link/<prefix in lower case>/input/
  2. runs `claude -p` there with auto/prove-prompt.md, BUILD_LIMIT=<builds> (build.sh
     refuses further `lake build`s) and a wall-clock limit of <hours>
  3. runs check.py on the case record the job wrote, and decides the verdict:
     「同じ性質」 only if the job wrote that verdict, stopped within the limits and
     check.py passed it; otherwise 「証明できず」 with the reason
  4. writes prove.json next to the case record, commits it, and copies it to the
     case directory

The worktree and branch are left for the publishing step (§5). Nothing here needs a
human decision.

Usage:
    python3 prove.py <case-dir> [--hours 4] [--builds 80] [--claude CMD] [--dry-run]
"""
import argparse
import json
import os
import shlex
import shutil
import signal
import string
import subprocess
import sys
import time
from dataclasses import asdict, dataclass, field
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PROMPT = HERE / 'prove-prompt.md'
SAME = '同じ性質'
NOT_PROVED = '証明できず'
CHECK_PASS = '合格'
ALLOWED_TOOLS = 'Bash Read Edit Write Glob Grep'
KILL_GRACE = 30
CO_AUTHOR = 'Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>'


@dataclass(frozen=True)
class Names:
    """Every name the job must use, fixed before it starts."""
    release: str
    stem: str
    case_id: str
    prefix: str
    git_branch: str
    worktree: Path
    case_md: str
    case_json: str
    tool_dir: str
    input_dir: str


@dataclass
class Outcome:
    patch: str
    branch: str
    verdict: str
    reasons: list[str] = field(default_factory=list)
    started: str = ''
    elapsed_s: int = 0
    builds: int = 0
    timed_out: bool = False
    claude_exit: int | None = None
    worktree: str = ''
    git_branch: str = ''
    check: dict | None = None


def names_for(manifest: dict, repo: Path) -> Names:
    release = manifest['branch'].split('/')[-1]
    stem = manifest['patch'].removesuffix('.patch')
    num = stem.removeprefix('CVE-').replace('-', '_')
    prefix = f'Deb{release.capitalize()}{num}'
    cases = f'research/backport-proof-debian/cases/{release}'
    tool_dir = f'research/c-semantics-link/{prefix.lower()}'
    return Names(release=release, stem=stem, case_id=f'auto-{release}-{num}', prefix=prefix,
                 git_branch=f'prove/{release}-{stem}',
                 worktree=repo.parent / f'{repo.name}-prove-{release}-{stem}',
                 case_md=f'{cases}/{stem}.md', case_json=f'{cases}/{stem}.json',
                 tool_dir=tool_dir, input_dir=f'{tool_dir}/input')


def render_prompt(manifest: dict, n: Names, hours: float, builds: int) -> str:
    values = {**{k: v for k, v in manifest.items() if isinstance(v, str)},
              'patch_sha256': manifest.get('debian_patch_sha256') or '',
              'hours': f'{hours:g}', 'builds': str(builds), **{
                  k: str(v) for k, v in asdict(n).items()}}
    return string.Template(PROMPT.read_text()).substitute(values)


def git(cwd: Path, *args: str) -> str:
    proc = subprocess.run(['git', '-C', str(cwd), *args], capture_output=True, text=True)
    if proc.returncode != 0:
        raise RuntimeError(f'git {" ".join(args)}: {proc.stderr.strip()}')
    return proc.stdout


def commit(wt: Path, paths: list[str], message: str) -> None:
    git(wt, 'add', '--', *paths)
    git(wt, 'commit', '-q', '-m', f'{message}\n\n{CO_AUTHOR}')


def prepare(case_dir: Path, n: Names, repo: Path) -> None:
    if n.worktree.exists():
        raise RuntimeError(f'{n.worktree} already exists; a job runs once per worktree')
    git(repo, 'worktree', 'add', '-q', '-b', n.git_branch, str(n.worktree), 'HEAD')
    lake = repo / 'research/c-semantics-link/lean/.lake'
    if lake.is_dir():
        shutil.copytree(lake, n.worktree / 'research/c-semantics-link/lean/.lake', symlinks=True)
    shutil.copytree(case_dir, n.worktree / n.input_dir)
    (n.worktree / n.case_md).parent.mkdir(parents=True, exist_ok=True)
    commit(n.worktree, [n.input_dir], f'chore: build.py inputs for {n.stem} ({n.release})')


def count_builds(wt: Path, case_id: str) -> int:
    log = wt / 'research/c-semantics-link/lean/build-log.tsv'
    if not log.exists():
        return 0
    return sum(1 for line in log.read_text().splitlines()
               if line.split('\t')[1:2] == [case_id])


def run_claude(cmd: list[str], prompt: str, wt: Path, builds: int, hours: float,
               log: Path) -> tuple[int | None, bool]:
    env = {**os.environ, 'BUILD_LIMIT': str(builds)}
    with log.open('w') as out:
        proc = subprocess.Popen(cmd, cwd=wt, env=env, stdin=subprocess.PIPE, stdout=out,
                                stderr=subprocess.STDOUT, text=True, start_new_session=True)
        try:
            proc.communicate(prompt, timeout=hours * 3600)
            return proc.returncode, False
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                proc.wait(KILL_GRACE)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
            return proc.returncode, True


def run_check(wt: Path, case_json: Path) -> dict:
    proc = subprocess.run([sys.executable, str(wt / 'research/backport-proof-debian/auto/check.py'),
                           str(case_json), '--lean-dir', str(wt / 'research/c-semantics-link/lean')],
                          capture_output=True, text=True)
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        return {'error': f'check.py exit {proc.returncode}: {proc.stderr.strip()[-1000:]}'}


def decide(out: Outcome, record: dict | None, check: dict | None, limit: int) -> None:
    """§3.6: 「同じ性質」 needs the job's own verdict, the limits, and §4."""
    if out.timed_out:
        out.reasons.append('時間の上限に達して止めた')
    if out.builds > limit:
        out.reasons.append(f'build の回数 {out.builds} が上限 {limit} を超えた')
    if record is None:
        out.reasons.append('件の記録（json）が無い')
    elif record.get('verdict') != SAME:
        out.reasons.append(f'ジョブの判定は「{record.get("verdict")}」')
    results = [c.get('result') for c in (check or {}).get('cases', [])]
    if record is not None and results != [CHECK_PASS]:
        why = (check or {}).get('error') or '; '.join(
            r for c in (check or {}).get('cases', []) for r in c.get('reasons', []))
        out.reasons.append(f'§4 の確認を通らない: {why}'[:2000])
    out.verdict = NOT_PROVED if out.reasons else SAME


def finish(case_dir: Path, n: Names, out: Outcome) -> None:
    # The record is published: paths inside the worktree become relative, and the
    # worktree itself is named without the machine's home directory.
    text = (json.dumps(asdict(out), ensure_ascii=False, indent=1) + '\n').replace(
        str(n.worktree) + '/', '').replace(str(n.worktree), n.worktree.name)
    rel = str(Path(n.case_json).with_suffix('.prove.json'))
    (n.worktree / rel).write_text(text)
    (case_dir / 'prove.json').write_text(text)
    # check.py's build appended a line to build-log.tsv; keep it with the verdict
    commit(n.worktree, [rel, 'research/c-semantics-link/lean/build-log.tsv'], f'docs: verdict for {n.stem} ({n.release}): {out.verdict}')


def prove(case_dir: Path, hours: float, builds: int, cmd: list[str], repo: Path) -> Outcome:
    manifest = json.loads((case_dir / 'manifest.json').read_text())
    n = names_for(manifest, repo)
    out = Outcome(patch=manifest['patch'], branch=manifest['branch'], verdict=NOT_PROVED,
                  started=time.strftime('%F %T'), worktree=str(n.worktree), git_branch=n.git_branch)
    prepare(case_dir, n, repo)
    t0 = time.monotonic()
    out.claude_exit, out.timed_out = run_claude(
        cmd, render_prompt(manifest, n, hours, builds), n.worktree, builds, hours,
        case_dir / 'claude.log')
    out.elapsed_s = int(time.monotonic() - t0)
    out.builds = count_builds(n.worktree, n.case_id)
    path = n.worktree / n.case_json
    record = json.loads(path.read_text()) if path.exists() else None
    out.check = run_check(n.worktree, path) if record is not None else None
    decide(out, record, out.check, builds)
    finish(case_dir, n, out)
    return out


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('case_dir', type=Path)
    ap.add_argument('--hours', type=float, default=4)
    ap.add_argument('--builds', type=int, default=80)
    ap.add_argument('--claude', default=f'claude -p --output-format json --permission-mode '
                                        f'acceptEdits --allowedTools "{ALLOWED_TOOLS}"')
    ap.add_argument('--repo', type=Path, default=REPO)
    ap.add_argument('--dry-run', action='store_true', help='print the names and prompt only')
    args = ap.parse_args(argv)
    manifest = json.loads((args.case_dir / 'manifest.json').read_text())
    if manifest.get('verdict') is not None:
        print(json.dumps({'patch': manifest['patch'], 'verdict': manifest['verdict'],
                          'reasons': ['build.py が判定を決めた件で、証明しない']}, ensure_ascii=False))
        return 0
    if args.dry_run:
        n = names_for(manifest, args.repo.resolve())
        print(json.dumps({k: str(v) for k, v in asdict(n).items()}, ensure_ascii=False, indent=1))
        print(render_prompt(manifest, n, args.hours, args.builds))
        return 0
    out = prove(args.case_dir.resolve(), args.hours, args.builds, shlex.split(args.claude),
                args.repo.resolve())
    print(json.dumps(asdict(out), ensure_ascii=False, indent=1))
    return 0 if out.verdict == SAME else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
