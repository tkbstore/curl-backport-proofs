"""PROTOCOL-auto §3.6 and §3.8: the proof job's names, limits and verdict."""
import os
import shutil
import subprocess
from pathlib import Path

import pytest

import check
import prove

HERE = Path(__file__).resolve().parents[1]
BUILD_SH = HERE.parents[0] / 'c-semantics-link' / 'lean' / 'build.sh'
MANIFEST = {'patch': 'CVE-2026-1965_2.patch', 'cve': 'CVE-2026-1965', 'branch': 'debian/bookworm',
            'debian_commit': 'c' * 40, 'upstream_fixed': 'a' * 40, 'upstream_parent': 'b' * 40,
            'debian_patch_sha256': 'd' * 64, 'target_file': 'lib/url.c',
            'debian_version': '7.88.1-10+deb12u15', 'base_tag': 'curl-7_88_1', 'verdict': None}


def names() -> prove.Names:
    return prove.names_for(MANIFEST, Path('/work/atrium-lean4'))


def test_names_are_per_release_and_per_patch() -> None:
    n = names()
    assert n.prefix == 'DebBookworm2026_1965_2'
    assert n.case_id == 'auto-bookworm-2026_1965_2'
    assert n.case_json == 'research/backport-proof-debian/cases/bookworm/CVE-2026-1965_2.json'
    assert n.worktree == Path('/work/atrium-lean4-prove-bookworm-CVE-2026-1965_2')
    assert n.git_branch == 'prove/bookworm-CVE-2026-1965_2'


def test_prefix_is_scanned_by_check() -> None:
    """check.py scans Deb*/GenDeb* modules for sorry and axiom; the job's modules must be among them."""
    n = names()
    assert check.SCANNED_MODULE.match(n.prefix + 'After')
    assert check.SCANNED_MODULE.match('Gen' + n.prefix + 'U1')


def test_prompt_fills_every_placeholder() -> None:
    text = prove.render_prompt(MANIFEST, names(), 4, 80)
    assert '$' not in text
    assert 'debian/bookworm' in text and 'prove/bookworm' not in text.split('\n')[0]
    assert 'build.sh auto-bookworm-2026_1965_2' in text and '80 回' in text


def outcome(**kw: object) -> prove.Outcome:
    return prove.Outcome(patch='p', branch='b', verdict='', **kw)


PASS = {'cases': [{'result': check.RESULT_PASS, 'reasons': []}]}
FAIL = {'cases': [{'result': check.RESULT_FAIL, 'reasons': ['許していない公理 [sorryAx]']}]}
SAME = {'verdict': prove.SAME}


def decided(out: prove.Outcome, record: dict | None, chk: dict | None) -> prove.Outcome:
    prove.decide(out, record, chk, 80)
    return out


def test_same_needs_the_jobs_verdict_and_the_check() -> None:
    assert decided(outcome(builds=12), SAME, PASS).verdict == prove.SAME


@pytest.mark.parametrize('out,record,chk,reason', [
    (outcome(), SAME, FAIL, '§4 の確認を通らない'),
    (outcome(), SAME, {'error': 'check.py exit 2'}, '§4 の確認を通らない'),
    (outcome(timed_out=True), SAME, PASS, '時間の上限'),
    (outcome(builds=81), SAME, PASS, '上限 80 を超えた'),
    (outcome(), None, None, '記録（json）が無い'),
    (outcome(), {'verdict': prove.NOT_PROVED}, PASS, 'ジョブの判定は「証明できず」'),
])
def test_anything_else_is_not_proved(out: prove.Outcome, record: dict | None, chk: dict | None,
                                     reason: str) -> None:
    res = decided(out, record, chk)
    assert res.verdict == prove.NOT_PROVED
    assert any(reason in r for r in res.reasons)


def test_count_builds_reads_only_this_case(tmp_path: Path) -> None:
    log = tmp_path / 'research/c-semantics-link/lean/build-log.tsv'
    log.parent.mkdir(parents=True)
    log.write_text('t\tauto-x\t1\nt\tauto-x\t0\nt\tauto-x-probe\t0\nt\tother\t0\n')
    assert prove.count_builds(tmp_path, 'auto-x') == 2
    assert prove.count_builds(tmp_path / 'none', 'auto-x') == 0


def test_published_record_has_no_machine_paths() -> None:
    wt = Path('/Users/someone/src/atrium-lean4-prove-bookworm-CVE-1')
    out = outcome(worktree=str(wt),
                  check={'cases': [{'case': f'{wt}/research/backport-proof-debian/cases/x.json'}]})
    text = prove.public_text(out, wt)
    assert '/Users/' not in text
    assert '"worktree": "atrium-lean4-prove-bookworm-CVE-1"' in text
    assert '"case": "research/backport-proof-debian/cases/x.json"' in text


def build_sh_in(tmp_path: Path, log: str) -> Path:
    shutil.copy(BUILD_SH, tmp_path / 'build.sh')
    (tmp_path / 'build-log.tsv').write_text(log)
    return tmp_path / 'build.sh'


def test_build_sh_refuses_at_the_limit(tmp_path: Path) -> None:
    script = build_sh_in(tmp_path, 't\tauto-x\t1\nt\tauto-x\t0\n')
    proc = subprocess.run(['sh', str(script), 'auto-x'], env={**os.environ, 'BUILD_LIMIT': '2'},
                          capture_output=True, text=True)
    assert proc.returncode == 3 and 'limit reached' in proc.stdout
    assert (tmp_path / 'build-log.tsv').read_text().count('auto-x') == 2  # nothing appended


def test_build_sh_limit_counts_only_this_case(tmp_path: Path) -> None:
    script = build_sh_in(tmp_path, 't\tauto-x-probe\t0\nt\tauto-y\t0\n')
    env = {**os.environ, 'BUILD_LIMIT': '1', 'PATH': f'{tmp_path}:{os.environ["PATH"]}'}
    (tmp_path / 'lake').write_text('#!/bin/sh\necho "Build completed successfully"\n')
    (tmp_path / 'lake').chmod(0o755)
    proc = subprocess.run(['sh', str(script), 'auto-x'], env=env, capture_output=True, text=True)
    assert proc.returncode == 0 and 'count[auto-x]=1' in proc.stdout


def test_the_time_limit_stops_the_whole_process_group(tmp_path: Path) -> None:
    """A job that outlives its limit is stopped, children included (lake runs as a child)."""
    marker = tmp_path / 'child-still-running'
    cmd = ['sh', '-c', f'(sleep 3; touch {marker}) & cat > /dev/null; sleep 60']
    code, timed_out = prove.run_claude(cmd, 'prompt', tmp_path, 80, 1 / 3600, tmp_path / 'log')
    assert timed_out and code is not None
    import time
    time.sleep(3.5)
    assert not marker.exists()


def test_a_job_that_ends_in_time_is_not_timed_out(tmp_path: Path) -> None:
    code, timed_out = prove.run_claude(['sh', '-c', 'cat > /dev/null; echo "$BUILD_LIMIT"'],
                                       'prompt', tmp_path, 7, 1, tmp_path / 'log')
    assert (code, timed_out) == (0, False)
    assert (tmp_path / 'log').read_text().strip() == '7'      # the limit reaches build.sh


def test_a_job_that_ended_abnormally_is_not_same(tmp_path: Path) -> None:
    out = decided(outcome(claude_exit=1), SAME, PASS)
    assert out.verdict == prove.NOT_PROVED and any('異常終了' in r for r in out.reasons)


def test_the_jobs_last_message_names_why_it_ended(tmp_path: Path) -> None:
    log = tmp_path / 'claude.log'
    log.write_text('noise\n{"type":"result","is_error":true,"result":"API Error: Connection lost while your computer was asleep"}\n')
    assert prove.last_result(log) == 'API Error: Connection lost while your computer was asleep'
    assert prove.last_result(tmp_path / 'none.log') == ''
