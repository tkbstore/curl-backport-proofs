"""Detect new Debian curl CVE patches and apply the mechanical rules.

Implements PROTOCOL-auto.md §2 (detection), §3.1 (upstream fix) and §3.2 (size).
Writes one JSON line per new or changed patch to stdout and updates the state
file. Nothing here needs a human decision.

Usage:
    python3 detect.py <branch> <state.json> [--dry-run]
    e.g. python3 detect.py debian/trixie state/debian-trixie.json
"""
import hashlib
import json
import re
import sys
import urllib.parse
import urllib.request
from dataclasses import asdict, dataclass
from pathlib import Path

SALSA = 'https://salsa.debian.org/api/v4/projects/debian%2Fcurl'
RAW = 'https://salsa.debian.org/debian/curl/-/raw'
CURL_CVE_JSON = 'https://curl.se/docs/{cve}.json'
MAX_LINES = 40
PATCH_RE = re.compile(r'^(CVE-\d{4}-\d+)(?:_\d+)?\.patch$')


@dataclass(frozen=True)
class Finding:
    branch: str
    commit: str
    patch: str
    cve: str
    sha256: str
    c_files: tuple[str, ...]
    changed_lines: int
    upstream_fixed: str | None
    verdict: str | None  # None means: go on to §3.3-3.4 and the proof


def fetch(url: str) -> bytes:
    with urllib.request.urlopen(url, timeout=60) as resp:
        return resp.read()


def branch_head(branch: str) -> str:
    data = json.loads(fetch(f'{SALSA}/repository/branches/{urllib.parse.quote(branch, safe="")}'))
    return data['commit']['id']


def cve_patches(commit: str) -> list[str]:
    url = f'{SALSA}/repository/tree?path=debian/patches&ref={commit}&per_page=100'
    return sorted(x['name'] for x in json.loads(fetch(url)) if PATCH_RE.match(x['name']))


def strip_prefix(path: str) -> str:
    """Drop the a/ b/ (git) or curl/ curl.orig/ (quilt -p2) directory prefix."""
    for prefix in ('a/', 'b/', 'curl.orig/', 'curl/'):
        if path.startswith(prefix):
            return path[len(prefix):]
    return path


def c_changes(patch: str) -> tuple[tuple[str, ...], int]:
    """C files touched (tests and docs excluded) and changed lines in them."""
    files: list[str] = []
    lines = 0
    current = None
    for line in patch.splitlines():
        if line.startswith('+++ '):
            path = strip_prefix(line[4:].split('\t')[0])
            is_c = path.endswith('.c') and not path.startswith(('tests/', 'docs/'))
            current = path if is_c else None
            if current and current not in files:
                files.append(current)
        elif current and line[:1] in '+-' and not line.startswith(('+++', '---')):
            lines += 1
    return tuple(files), lines


def upstream_fixed(cve: str) -> list[str]:
    try:
        data = json.loads(fetch(CURL_CVE_JSON.format(cve=cve)))
    except OSError:
        return []
    return [ev['fixed']
            for aff in data.get('affected', [])
            for rng in aff.get('ranges', []) if rng.get('type') == 'GIT'
            for ev in rng.get('events', []) if 'fixed' in ev]


def judge(branch: str, commit: str, name: str, text: bytes) -> Finding:
    cve = PATCH_RE.match(name).group(1)
    files, lines = c_changes(text.decode('utf-8', 'replace'))
    fixed = upstream_fixed(cve)
    verdict = None
    if len(fixed) != 1:
        verdict = '上流の修正を特定できない'
    elif not files:
        verdict = 'C の変更が無い'
    elif len(files) != 1 or lines > MAX_LINES:
        verdict = '対象外（大きさ）'
    return Finding(branch, commit, name, cve, hashlib.sha256(text).hexdigest(),
                   files, lines, fixed[0] if len(fixed) == 1 else None, verdict)


def main() -> None:
    args = [a for a in sys.argv[1:] if a != '--dry-run']
    if len(args) != 2:
        sys.exit(__doc__)
    branch, state_path = args[0], Path(args[1])
    state = json.loads(state_path.read_text()) if state_path.exists() else {'patches': {}}
    commit = branch_head(branch)
    seen: dict[str, str] = state['patches']
    for name in cve_patches(commit):
        text = fetch(f'{RAW}/{commit}/debian/patches/{name}')
        digest = hashlib.sha256(text).hexdigest()
        if seen.get(name) == digest:
            continue
        print(json.dumps(asdict(judge(branch, commit, name, text)), ensure_ascii=False))
        seen = {**seen, name: digest}
    if '--dry-run' not in sys.argv:
        state_path.parent.mkdir(parents=True, exist_ok=True)
        state_path.write_text(json.dumps({'commit': commit, 'patches': seen}, indent=1) + '\n')


if __name__ == '__main__':
    main()
