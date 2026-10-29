"""Make auto/ and publish/ importable; they are scripts, not a package."""
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
for sub in ('auto', 'publish'):
    sys.path.insert(0, str(ROOT / sub))


def run_git(cwd: Path, *args: str) -> str:
    return subprocess.run(['git', '-C', str(cwd), *args], check=True,
                          capture_output=True, text=True).stdout


@pytest.fixture
def git_repo(tmp_path: Path) -> Path:
    repo = tmp_path / 'repo'
    repo.mkdir()
    run_git(repo, 'init', '-q', '-b', 'main')
    run_git(repo, 'config', 'user.email', 'test@example.invalid')
    run_git(repo, 'config', 'user.name', 'test')
    run_git(repo, 'config', 'core.hooksPath', '/dev/null')  # no global hooks in tests
    return repo
