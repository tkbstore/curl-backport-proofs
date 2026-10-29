"""PROTOCOL-auto §3.4: how much of the upstream fix Debian's patch contains."""
import pytest

import mechanism

OPEN = {'patch': 'CVE-2026-0001.patch', 'verdict': None, 'upstream_fixed': 'a' * 40,
        'commit': 'c' * 40}


def with_share(monkeypatch: pytest.MonkeyPatch, up_in_deb_at_08: float) -> None:
    rev = [1.0, up_in_deb_at_08, 0.0]  # shares at THRESHOLDS (0.6, 0.8, 0.9)
    monkeypatch.setattr(mechanism, 'measure', lambda f: (['d'], ['u'], [1.0, 1.0, 1.0], rev))


def test_the_share_is_read_at_0_8() -> None:
    assert mechanism.THRESHOLDS[mechanism.THRESHOLDS.index(mechanism.MATCH_AT)] == 0.8


@pytest.mark.parametrize('share,verdict', [(0.5, None), (1.0, None), (0.49, '上流と仕組みが違う'),
                                           (0.0, '上流と仕組みが違う')])
def test_boundary(monkeypatch: pytest.MonkeyPatch, share: float, verdict: str | None) -> None:
    with_share(monkeypatch, share)
    out = mechanism.judge(OPEN)
    assert out.get('verdict') == verdict
    assert out['up_in_deb'] == share


def test_different_verdict_carries_both_added_lines(monkeypatch: pytest.MonkeyPatch) -> None:
    with_share(monkeypatch, 0.0)
    out = mechanism.judge(OPEN)
    assert out['deb_added'] == ['d'] and out['up_added'] == ['u']
    assert '0.00' in out['detail']


def test_decided_findings_pass_through(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(mechanism, 'measure', lambda f: pytest.fail('must not measure'))
    decided = {**OPEN, 'verdict': '対象外（大きさ）'}
    assert mechanism.judge(decided) == decided


def test_judge_does_not_change_its_input(monkeypatch: pytest.MonkeyPatch) -> None:
    with_share(monkeypatch, 0.0)
    before = dict(OPEN)
    mechanism.judge(OPEN)
    assert OPEN == before


def test_added_lines_skip_tests_braces_and_whitespace() -> None:
    diff = '\n'.join(['+++ b/lib/url.c', '+  if(x)   return 1;', '+{', '+}', '+',
                      '+++ b/tests/unit/u.c', '+  check();'])
    assert mechanism.added(diff, mechanism.is_c_source) == ['if(x) return 1;']


def test_best_and_shares() -> None:
    assert mechanism.best('abc', []) == 0.0
    assert mechanism.best('abc', ['abc', 'xyz']) == 1.0
    assert mechanism.shares([]) == [0.0, 0.0, 0.0]
    assert mechanism.shares([1.0, 0.7]) == [1.0, 0.5, 0.5]
