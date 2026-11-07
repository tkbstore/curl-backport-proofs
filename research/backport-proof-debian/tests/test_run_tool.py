"""run.tool: a tool that failed is never read as one that had nothing to report."""
from pathlib import Path

import pytest

import run

CRASH = 'import sys\nprint(\'{"patch": "A.patch"}\', flush=True)\nraise OSError("no network")\n'


def with_tool(monkeypatch: pytest.MonkeyPatch, tmp_path: Path, name: str, body: str) -> None:
    (tmp_path / name).write_text(body)
    monkeypatch.setattr(run, 'HERE', tmp_path)


@pytest.mark.parametrize('name', ['detect.py', 'mechanism.py', 'build.py'])
def test_an_uncaught_exception_raises_even_after_partial_output(
        monkeypatch: pytest.MonkeyPatch, tmp_path: Path, name: str) -> None:
    with_tool(monkeypatch, tmp_path, name, CRASH)
    with pytest.raises(RuntimeError, match=f'(?s){name} exit 1: .*OSError: no network'):
        run.tool(name)


def test_a_usage_exit_raises(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    with_tool(monkeypatch, tmp_path, 'detect.py', 'import sys\nsys.exit("usage")\n')
    with pytest.raises(RuntimeError, match='detect.py exit 1: usage'):
        run.tool('detect.py')


def test_nothing_printed_with_exit_0_is_nothing_to_do(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    with_tool(monkeypatch, tmp_path, 'detect.py', '')
    assert run.tool('detect.py') == []


def test_json_lines_are_read(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    with_tool(monkeypatch, tmp_path, 'mechanism.py', 'print(\'{"a": 1}\')\nprint(\'{"a": 2}\')\n')
    assert run.tool('mechanism.py') == [{'a': 1}, {'a': 2}]


def test_prove_exit_1_with_its_document_is_a_verdict(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    body = 'import sys\nprint(\'{\\n "verdict": "証明できず"\\n}\')\nsys.exit(1)\n'
    with_tool(monkeypatch, tmp_path, 'prove.py', body)
    assert run.tool('prove.py') == [{'verdict': '証明できず'}]


def test_prove_crash_raises(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    with_tool(monkeypatch, tmp_path, 'prove.py', 'raise KeyError("manifest")\n')
    with pytest.raises(RuntimeError, match='(?s)prove.py exit 1: .*KeyError'):
        run.tool('prove.py')


def test_prove_other_exit_raises(monkeypatch: pytest.MonkeyPatch, tmp_path: Path) -> None:
    with_tool(monkeypatch, tmp_path, 'prove.py', 'import sys\nprint("{}")\nsys.exit(2)\n')
    with pytest.raises(RuntimeError, match='prove.py exit 2'):
        run.tool('prove.py')
