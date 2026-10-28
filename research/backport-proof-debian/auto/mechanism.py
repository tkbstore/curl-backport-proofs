"""Measure how similar Debian's patch is to the upstream fix (PROTOCOL-auto.md §3.4).

For each patch: the lines Debian's patch adds to C files, and the lines the
upstream fix commit adds to C files (tests and docs excluded). For every
Debian line, the best difflib ratio against any upstream line. Prints the
share of Debian lines whose best match is at least each threshold
(deb_in_up), and the same with the roles swapped (up_in_deb).

With --judge, reads and writes detect.py's JSON lines instead of a table: a finding
that is still open gets `up_in_deb` (share at 0.8) and, below PROCEED_AT, the verdict
「上流と仕組みが違う」. Findings that already have a verdict pass through unchanged.

Usage:
    python3 detect.py debian/trixie st.json --dry-run | python3 mechanism.py [--judge]
"""
import difflib
import json
import re
import subprocess
import sys
import urllib.request

from detect import strip_prefix

RAW = 'https://salsa.debian.org/debian/curl/-/raw/{commit}/debian/patches/{patch}'
THRESHOLDS = (0.6, 0.8, 0.9)
MATCH_AT = 0.8  # PROTOCOL-auto §3.4: a line counts when its best ratio is at least this
PROCEED_AT = 0.5  # §3.4: prove when up_in_deb is at least this
DIFFERENT = '上流と仕組みが違う'


def fetch(url: str) -> bytes:
    req = urllib.request.Request(url, headers={'User-Agent': 'backport-proof'})
    with urllib.request.urlopen(req, timeout=60) as resp:
        return resp.read()


def is_c_source(path: str) -> bool:
    return path.endswith(('.c', '.h')) and not path.startswith(('tests/', 'docs/'))


def norm(line: str) -> str:
    return re.sub(r'\s+', ' ', line).strip()


def added(diff_text: str, path_ok) -> list[str]:
    out: list[str] = []
    keep = False
    for line in diff_text.splitlines():
        if line.startswith('+++ '):
            path = strip_prefix(line[4:].split('\t')[0])
            keep = path_ok(path)
        elif keep and line.startswith('+') and not line.startswith('+++'):
            text = norm(line[1:])
            if text and text not in ('{', '}'):
                out.append(text)
    return out


def github_commit(sha: str) -> dict:
    """Fetch through the authenticated gh CLI; the anonymous API allows 60 calls an hour."""
    out = subprocess.run(['gh', 'api', f'repos/curl/curl/commits/{sha}'],
                         capture_output=True, text=True, check=True)
    return json.loads(out.stdout)


def upstream_added(sha: str) -> list[str]:
    data = github_commit(sha)
    out: list[str] = []
    for f in data['files']:
        if is_c_source(f['filename']) and 'patch' in f:
            out += added('+++ b/' + f['filename'] + '\n' + f['patch'], lambda p: True)
    return out


def best(line: str, pool: list[str]) -> float:
    return max((difflib.SequenceMatcher(None, line, p).ratio() for p in pool), default=0.0)


def shares(scores: list[float]) -> list[float]:
    return [sum(s >= t for s in scores) / len(scores) if scores else 0.0
            for t in THRESHOLDS]


def measure(f: dict) -> tuple[list[str], list[str], list[float], list[float]]:
    deb = added(fetch(RAW.format(**f)).decode('utf-8', 'replace'), is_c_source)
    up = upstream_added(f['upstream_fixed'])
    return deb, up, shares([best(line, up) for line in deb]), shares([best(line, deb) for line in up])


def judge(f: dict) -> dict:
    if f.get('verdict') is not None:
        return f
    deb, up, _, rev = measure(f)
    share = rev[THRESHOLDS.index(MATCH_AT)]
    if share >= PROCEED_AT:
        return {**f, 'up_in_deb': share}
    return {**f, 'up_in_deb': share, 'verdict': DIFFERENT,
            'detail': f'up_in_deb {share:.2f} < {PROCEED_AT}',
            'deb_added': deb, 'up_added': up}


def main() -> None:
    as_json = '--judge' in sys.argv[1:]
    for raw in sys.stdin:
        if not raw.strip():
            continue
        f = json.loads(raw)
        if as_json:
            print(json.dumps(judge(f), ensure_ascii=False), flush=True)
            continue
        if not f['upstream_fixed']:
            continue
        deb, up, fwd, rev = measure(f)
        print(f"{f['patch']:24} deb+{len(deb):3} up+{len(up):4} "
              + 'deb_in_up ' + ' '.join(f'{s:.2f}' for s in fwd)
              + ' | up_in_deb ' + ' '.join(f'{s:.2f}' for s in rev))


if __name__ == '__main__':
    main()
