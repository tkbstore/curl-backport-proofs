"""PROTOCOL-auto §3.7 and §5: records decided by rule, the state, and the published copy."""
import json
from pathlib import Path

import pytest

import check
import run

publish = pytest.importorskip('publish')  # not part of the public copy
from conftest import run_git

FINDING = {'branch': 'debian/bookworm', 'commit': 'c' * 40, 'patch': 'CVE-2026-5773.patch',
           'cve': 'CVE-2026-5773', 'sha256': 's' * 64, 'c_files': ['lib/smb.c'], 'changed_lines': 6,
           'upstream_fixed': 'a' * 40, 'verdict': '上流と仕組みが違う', 'up_in_deb': 0.0,
           'detail': 'up_in_deb 0.00 < 0.5', 'deb_added': ['x'], 'up_added': ['y']}


def test_a_rule_record_is_read_by_check_as_having_no_theorems(tmp_path: Path) -> None:
    path = tmp_path / 'r.json'
    path.write_text(json.dumps(run.record_for(FINDING), ensure_ascii=False))
    res = check.judge(check.load_case(path), True, check.ProbeOutput({}, {}, {}, ()), tmp_path)
    assert res.result == check.RESULT_NO_THEOREMS


def test_a_rule_record_keeps_the_evidence() -> None:
    rec = run.record_for(FINDING)
    assert rec['debian_commit'] == FINDING['commit']
    assert rec['up_in_deb'] == 0.0 and rec['c_files'] == ['lib/smb.c'] and rec['changed_lines'] == 6
    assert rec['scope'] is None and rec['theorems'] == {}


def pass_with(monkeypatch: pytest.MonkeyPatch, tmp_path: Path, judged: list[dict],
              proved: set[str], budget: int) -> tuple[dict, list[str]]:
    """run_branch with detect/mechanism/git/prove replaced; returns the new state."""
    public, work = tmp_path / 'pub', tmp_path / 'work'
    (public / 'state').mkdir(parents=True)
    work.mkdir()
    (public / 'state' / 'debian-bookworm.json').write_text(
        json.dumps({'commit': 'old', 'patches': {'CVE-0.patch': 'z'}}))
    monkeypatch.setattr(run, 'tool', lambda name, *a, **k: judged if name == 'mechanism.py' else [])
    monkeypatch.setattr(run, 'commit', lambda paths, msg: None)
    monkeypatch.setattr(run, 'write_record', lambda f: 'x.json')
    monkeypatch.setattr(run, 'prove_one', lambda f, out, log: f['patch'] in proved)
    log: list[str] = []
    run.run_branch('debian/bookworm', public, work, budget, log)
    return json.loads((work / 'state' / 'debian-bookworm.json').read_text()), log


def open_finding(name: str) -> dict:
    return {**FINDING, 'patch': name, 'sha256': name, 'verdict': None}


def test_state_holds_only_what_reached_a_verdict(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    judged = [FINDING, open_finding('A.patch'), open_finding('B.patch'), open_finding('C.patch')]
    state, log = pass_with(monkeypatch, tmp_path, judged, proved={'A.patch'}, budget=2)
    assert state['commit'] == 'c' * 40
    assert set(state['patches']) == {'CVE-0.patch', 'CVE-2026-5773.patch', 'A.patch'}
    assert any('C.patch: left for a later pass' in line for line in log)


def test_no_findings_keeps_the_previous_state(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    state, _ = pass_with(monkeypatch, tmp_path, [], proved=set(), budget=1)
    assert state == {'commit': 'old', 'patches': {'CVE-0.patch': 'z'}}


def write_case(root: Path, rel: str, rec: dict) -> None:
    path = root / publish.CASES / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(rec, ensure_ascii=False))


def test_records_find_the_notes_and_skip_prove_files(tmp_path: Path) -> None:
    base = {'branch': 'debian/trixie', 'verdict': '同じ性質'}
    write_case(tmp_path, 'CVE-2026-1965_2.json', {**base, 'patch': 'CVE-2026-1965_2.patch', 'cve': 'CVE-2026-1965'})
    (tmp_path / publish.CASES / 'CVE-2026-1965.md').write_text('notes')
    write_case(tmp_path, 'bookworm/CVE-1.json', {**base, 'branch': 'debian/bookworm', 'patch': 'CVE-1.patch', 'cve': 'CVE-1'})
    (tmp_path / publish.CASES / 'bookworm/CVE-1.md').write_text('notes')
    write_case(tmp_path, 'bookworm/CVE-1.prove.json', {'verdict': 'x'})
    recs = publish.records(tmp_path)
    assert [(r['release'], r['patch']) for r in recs] == [('bookworm', 'CVE-1.patch'), ('trixie', 'CVE-2026-1965_2.patch')]
    assert recs[1]['notes'].endswith('cases/CVE-2026-1965.md')
    assert recs[0]['notes'].endswith('cases/bookworm/CVE-1.md')


def test_rule_verdicts_show_files_and_lines() -> None:
    rec = {'notes': None, 'detail': '', 'c_files': ['lib/a.c', 'lib/b.c'], 'changed_lines': 47}
    assert publish.note(rec) == '`lib/a.c`, `lib/b.c` 47 lines'


def test_a_pipe_in_a_cell_does_not_break_the_table() -> None:
    rec = {'release': 'r', 'patch': 'p', 'verdict': 'v', 'scope': None, 'external_specs': None,
           'notes': None, 'detail': 'a | b', 'c_files': None, 'changed_lines': None}
    row = publish.verdicts_md([rec]).splitlines()[-1]
    assert row.count('|') == 9


def test_replace_contents_keeps_git_state_and_work_toml(tmp_path: Path) -> None:
    public, snap = tmp_path / 'pub', tmp_path / 'snap'
    for d in ('.git', 'state', 'old'):
        (public / d).mkdir(parents=True)
    (public / 'work.toml').write_text('[publish]\n')
    (public / 'stale.md').write_text('x')
    (snap / 'research').mkdir(parents=True)
    (snap / 'README.md').write_text('new')
    publish.replace_contents(public, snap)
    assert sorted(p.name for p in public.iterdir()) == ['.git', 'README.md', 'research', 'state', 'work.toml']


def test_release_is_declared_only_after_the_root_is_on_the_remote(git_repo: Path, tmp_path: Path) -> None:
    (git_repo / 'a').write_text('a')
    run_git(git_repo, 'add', 'a')
    run_git(git_repo, 'commit', '-q', '-m', 'docs: root')
    publish.declare_release(git_repo)
    assert not (git_repo / 'work.toml').exists()          # nothing pushed yet

    remote = tmp_path / 'remote.git'
    run_git(tmp_path, 'init', '-q', '--bare', str(remote))
    run_git(git_repo, 'remote', 'add', 'origin', str(remote))
    run_git(git_repo, 'push', '-q', 'origin', 'main')
    root = run_git(git_repo, 'rev-parse', 'HEAD').strip()
    publish.declare_release(git_repo)
    assert f'released_at = "{root}"' in (git_repo / 'work.toml').read_text()

    (git_repo / 'work.toml').write_text('kept\n')
    publish.declare_release(git_repo)
    assert (git_repo / 'work.toml').read_text() == 'kept\n'


def test_read_back_comes_from_prove_or_review_files(tmp_path: Path) -> None:
    base = {'branch': 'debian/trixie', 'verdict': '同じ性質'}
    write_case(tmp_path, 'CVE-1.json', {**base, 'patch': 'CVE-1.patch', 'cve': 'CVE-1'})
    write_case(tmp_path, 'CVE-1.review.json', {'status': '指摘あり', 'problems': ['p0_states_bug'], 'summary': 's'})
    write_case(tmp_path, 'bookworm/CVE-2.json', {**base, 'branch': 'debian/bookworm', 'patch': 'CVE-2.patch', 'cve': 'CVE-2'})
    write_case(tmp_path, 'bookworm/CVE-2.prove.json', {'verdict': '同じ性質', 'review': {'status': '指摘なし', 'problems': []}})
    write_case(tmp_path, 'CVE-3.json', {**base, 'patch': 'CVE-3.patch', 'cve': 'CVE-3'})
    recs = {r['patch']: r for r in publish.records(tmp_path)}
    assert len(recs) == 3
    assert publish.readback(recs['CVE-1.patch']) == '指摘あり (p0_states_bug)'
    assert publish.readback(recs['CVE-2.patch']) == '指摘なし'
    assert publish.readback(recs['CVE-3.patch']) == '—'


def test_p0_on_fixed_cell_names_the_theorem() -> None:
    assert publish.p0_on_fixed({}) == '—'
    rec = {'p0_on_fixed': '成立', 'p0_on_fixed_theorems': ['A.b']}
    assert publish.p0_on_fixed(rec) == '成立 (`A.b`)'


def _committed_repo(git_repo: Path) -> Path:
    (git_repo / 'a.txt').write_text('a\n')
    run_git(git_repo, 'add', 'a.txt')
    run_git(git_repo, 'commit', '-q', '-m', 'init')
    return git_repo


def test_a_lock_of_a_dead_pass_is_replaced(tmp_path: Path) -> None:
    lock, log = tmp_path / 'run.lock', []
    lock.write_text('999999')  # no such process
    assert run.take_lock(lock, log)
    assert lock.read_text() == str(__import__('os').getpid())
    assert log and 'replaced' in log[0]


def test_a_lock_of_a_live_pass_is_kept(tmp_path: Path) -> None:
    lock = tmp_path / 'run.lock'
    lock.write_text(str(__import__('os').getpid()))
    assert not run.take_lock(lock, [])


def test_uncommitted_changes_are_stashed_not_lost(monkeypatch: pytest.MonkeyPatch, git_repo: Path,
                                                  tmp_path: Path) -> None:
    repo = _committed_repo(git_repo)
    monkeypatch.setattr(run, 'REPO', repo)
    (repo / 'a.txt').write_text('changed\n')
    log: list[str] = []
    run.recover(tmp_path / 'work', log)
    assert run_git(repo, 'status', '--porcelain') == ''
    assert 'leftover' in run_git(repo, 'stash', 'list')
    assert 'stashed' in log[0]


def test_a_leftover_proof_worktree_is_moved_and_its_name_freed(monkeypatch: pytest.MonkeyPatch,
                                                               git_repo: Path, tmp_path: Path) -> None:
    repo = _committed_repo(git_repo)
    monkeypatch.setattr(run, 'REPO', repo)
    wt = tmp_path / 'repo-prove-trixie-CVE-1'
    run_git(repo, 'worktree', 'add', '-q', '-b', 'prove/trixie-CVE-1', str(wt), 'HEAD')
    (wt / 'half-done.lean').write_text('-- work of the interrupted job\n')
    log: list[str] = []
    run.recover(tmp_path / 'work', log)
    assert not wt.exists()
    moved = list((tmp_path / 'work' / 'leftover').iterdir())
    assert len(moved) == 1 and (moved[0] / 'half-done.lean').exists()
    branches = run_git(repo, 'branch', '--list')
    assert 'prove/trixie-CVE-1' not in branches and 'leftover/trixie-CVE-1-' in branches
    assert run.prove_worktrees() == []


def test_a_clean_checkout_is_left_alone(monkeypatch: pytest.MonkeyPatch, git_repo: Path, tmp_path: Path) -> None:
    repo = _committed_repo(git_repo)
    monkeypatch.setattr(run, 'REPO', repo)
    log: list[str] = []
    run.recover(tmp_path / 'work', log)
    assert log == [] and run_git(repo, 'stash', 'list') == ''


def test_last_run_hides_the_home_directory(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    monkeypatch.setattr(run.Path, 'home', lambda: tmp_path)
    rec = run.last_run('s', 'f', [f'{tmp_path}/work: built'], RuntimeError(f'git: {tmp_path}/x failed'))
    assert rec['ok'] is False and rec['started'] == 's' and rec['finished'] == 'f'
    assert str(tmp_path) not in json.dumps(rec) and rec['log'] == ['~/work: built']
    assert rec['error'].startswith('RuntimeError: git: ~/x')


def test_a_successful_pass_records_no_error() -> None:
    rec = run.last_run('s', 'f', ['publish: abc'], None)
    assert rec['ok'] is True and rec['error'] is None


def test_a_failed_pass_commits_only_its_report(git_repo: Path) -> None:
    public = _committed_repo(git_repo)
    (public / 'a.txt').write_text('half-written by an interrupted publish\n')
    run.report_failure(public, {'ok': False, 'error': 'boom'}, push=False)
    shown = run_git(public, 'show', '--name-only', '--format=%s', 'HEAD')
    assert shown.split()[-1] == 'state/last-run.json' and 'a.txt' not in shown
    assert json.loads((public / 'state' / 'last-run.json').read_text())['error'] == 'boom'
    assert 'a.txt' in run_git(public, 'status', '--porcelain')  # left as it was, not committed


@pytest.mark.parametrize('rec,expected', [
    ({'claude_exit': 1, 'timed_out': False}, True),    # e.g. the connection was lost while the Mac slept
    ({'claude_exit': 0, 'timed_out': False}, False),
    ({'claude_exit': -15, 'timed_out': True}, False),  # the time limit is a verdict, not an interruption
    ({}, False),
])
def test_interrupted(rec: dict, expected: bool) -> None:
    assert run.interrupted(rec) is expected


def test_an_interrupted_verdict_is_dropped_from_the_state_to_be_retried(monkeypatch: pytest.MonkeyPatch,
                                                                       tmp_path: Path) -> None:
    monkeypatch.setattr(run, 'REPO', tmp_path)
    case = tmp_path / run.CASES / 'bookworm'
    case.mkdir(parents=True)
    (case / 'A.prove.json').write_text(json.dumps({'claude_exit': 1, 'timed_out': False}))
    (case / 'B.prove.json').write_text(json.dumps({'claude_exit': 0, 'timed_out': False}))
    patches = {'A.patch': 'a', 'B.patch': 'b', 'C.patch': 'c'}
    work = tmp_path / 'work'
    assert run.retry_interrupted('debian/bookworm', patches, work, []) == {'B.patch': 'b', 'C.patch': 'c'}
    for stamp in ('20261031T030000', '20261101T030000'):  # the third try was the last one
        (work / 'leftover' / f'bookworm-A-{stamp}').mkdir(parents=True)
    assert run.retry_interrupted('debian/bookworm', patches, work, []) == patches


def test_an_interrupted_job_is_retried_until_the_third_time(tmp_path: Path) -> None:
    (tmp_path / 'leftover').mkdir()
    assert run.retries_left(tmp_path, 'bookworm-CVE-1')
    for stamp in ('20261031T030000', '20261101T030000'):
        (tmp_path / 'leftover' / f'bookworm-CVE-1-{stamp}').mkdir()
    (tmp_path / 'leftover' / 'bookworm-CVE-10-20261031T030000').mkdir()  # another patch
    assert not run.retries_left(tmp_path, 'bookworm-CVE-1')
