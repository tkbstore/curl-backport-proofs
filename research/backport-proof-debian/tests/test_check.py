"""PROTOCOL-auto §4: the mechanical checks must not let a cheat through."""
from pathlib import Path

import pytest

import check

STD = ['propext', 'Classical.choice', 'Quot.sound']
THMS = {'U1': ['X.p1u'], 'U0': ['X.p0u'], 'D1': ['X.p1d'], 'D0': ['X.p0d']}
DFUN = {'D1': ['X_d1.f_g'], 'D0': ['X_d0.f_g']}


def scan(tmp_path: Path, src: str) -> list[str]:
    path = tmp_path / 'DebX.lean'
    path.write_text(src)
    return check.forbidden_in(path)


@pytest.mark.parametrize('src', [
    'theorem t : True := by sorry',
    'theorem t : True := by\n  admit',
    'example : 2 + 2 = 4 := by native_decide',
    'example : x = y := by bv_decide',
    'axiom cheat : False',
    '@[simp] axiom cheat : False',
    'private axiom cheat : False',
    'noncomputable axiom cheat : Nat',
    '/- nested /- comment -/ still a comment -/ theorem t : True := sorry',
])
def test_cheats_are_found(tmp_path: Path, src: str) -> None:
    assert scan(tmp_path, src)


@pytest.mark.parametrize('src', [
    '-- sorry, this is a comment',
    '/- admit -/ theorem t : True := trivial',
    'def s := "sorry"',
    "def q := '\"'  -- a quote char, then sorry in a comment",
    'theorem no_sorry_here : True := trivial',
    'theorem uses_axiom_name : myaxiom = 1 := rfl',
    'theorem t : x.sorry_free = 1 := rfl',
])
def test_lookalikes_are_not_cheats(tmp_path: Path, src: str) -> None:
    assert scan(tmp_path, src) == []


def test_reported_line_is_the_declaration(tmp_path: Path) -> None:
    assert scan(tmp_path, 'theorem a : True := trivial\n\naxiom b : False\n') == ['DebX.lean:3: axiom の宣言']


@pytest.mark.parametrize('text,expected', [
    ("'X.t' does not depend on any axioms", []),
    ("'X.t' depends on axioms: [propext, Classical.choice,\n Quot.sound]", STD),
    ('unknown identifier', None),
])
def test_parse_axioms(text: str, expected: list[str] | None) -> None:
    assert check.parse_axioms(text) == expected


def case(**kw: object) -> check.Case:
    base = dict(path='c.json', patch='CVE-1.patch', verdict=check.SAME, lean_modules=('DebX',),
                theorems={k: tuple(v) for k, v in THMS.items()},
                d_functions={k: tuple(v) for k, v in DFUN.items()})
    return check.Case(**{**base, **kw})


def probe(axioms: dict | None = None, checks: dict | None = None) -> check.ProbeOutput:
    all_thms = [t for ts in THMS.values() for t in ts]
    ax = {t: STD + ['CC.externalFunctionsSem'] for t in all_thms}
    ck = {t: f'{t} : spec X_u.f_g' for t in all_thms}
    ck.update({'X.p1d': 'X.p1d : spec X_d1.f_g', 'X.p0d': 'X.p0d : spec X_d0.f_g'})
    return check.ProbeOutput({**ax, **(axioms or {})}, {**ck, **(checks or {})}, {}, ())


@pytest.fixture
def lean_dir(tmp_path: Path) -> Path:
    (tmp_path / 'DebX.lean').write_text('theorem p : True := trivial\n')
    return tmp_path


def test_a_clean_case_passes(lean_dir: Path) -> None:
    res = check.judge(case(), True, probe(), lean_dir)
    assert res.result == check.RESULT_PASS, res.reasons


@pytest.mark.parametrize('kw,pr,built', [
    ({}, probe(axioms={'X.p1d': STD + ['sorryAx']}), True),        # a sorry hidden from the scan
    ({}, probe(axioms={'X.p0u': None}), True),                      # theorem missing
    ({}, probe(checks={'X.p1d': 'X.p1d : spec X_u.f_g'}), True),   # D theorem about U's function
    ({'theorems': {k: tuple(v) for k, v in THMS.items() if k != 'D0'}}, probe(), True),
    ({'d_functions': {}}, probe(), True),
    ({'lean_modules': ()}, probe(), True),
    ({}, probe(), False),                                           # lake build failed
])
def test_any_gap_fails(lean_dir: Path, kw: dict, pr: check.ProbeOutput, built: bool) -> None:
    assert check.judge(case(**kw), built, pr, lean_dir).result == check.RESULT_FAIL


def test_a_name_that_only_starts_like_the_d_function_does_not_count(lean_dir: Path) -> None:
    pr = probe(checks={'X.p1d': 'X.p1d : spec X_d1.f_g_helper'})
    assert check.judge(case(), True, pr, lean_dir).result == check.RESULT_FAIL


def test_forbidden_word_in_an_imported_deb_module_fails(lean_dir: Path) -> None:
    (lean_dir / 'DebX.lean').write_text('import DebXCommon\ntheorem p : True := trivial\n')
    (lean_dir / 'DebXCommon.lean').write_text('theorem helper : False := sorry\n')
    assert check.judge(case(), True, probe(), lean_dir).result == check.RESULT_FAIL


def test_a_verdict_without_theorems_is_reported_as_such(lean_dir: Path) -> None:
    res = check.judge(case(verdict='上流と仕組みが違う', theorems={}, d_functions={}), True, probe(), lean_dir)
    assert res.result == check.RESULT_NO_THEOREMS


def test_p0_on_fixed_theorems_get_the_axiom_check(lean_dir: Path) -> None:
    thms = {**{k: tuple(v) for k, v in THMS.items()}, check.CROSS_SLOT: ('X.p0x',)}
    kw = dict(theorems=thms, p0_on_fixed=check.CROSS_HOLDS)
    assert check.judge(case(**kw), True, probe(axioms={'X.p0x': STD}), lean_dir).result == check.RESULT_PASS
    bad = probe(axioms={'X.p0x': STD + ['sorryAx']})
    assert check.judge(case(**kw), True, bad, lean_dir).result == check.RESULT_FAIL


def test_p0_on_fixed_holds_without_a_theorem_fails(lean_dir: Path) -> None:
    res = check.judge(case(p0_on_fixed=check.CROSS_HOLDS), True, probe(), lean_dir)
    assert res.result == check.RESULT_FAIL


def test_p0_on_fixed_must_be_a_known_word(tmp_path: Path) -> None:
    rec = tmp_path / 'c.json'
    rec.write_text('{"patch": "p", "verdict": "同じ性質", "p0_on_fixed": "たぶん"}')
    with pytest.raises(ValueError):
        check.load_case(rec)
