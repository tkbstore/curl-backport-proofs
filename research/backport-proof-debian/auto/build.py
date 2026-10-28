"""Build the four C sources a proof needs (PROTOCOL-auto.md §3.3).

Reads detect.py's JSON lines on stdin. For every finding whose verdict is
still open, writes under <out>/<patch name without .patch>/:

    U0/<path>, U1/<path>   upstream C files changed by the fix, at the fix's
                           parent and at the fix (tests/ and docs/ excluded)
    D0/<path>, D1/<path>   Debian's base release with debian/patches/series
                           applied in order: D0 up to just before this patch,
                           D1 up to and including it. Only the parts of each
                           patch touching the target .c file are applied.
    functions/{U0,U1,D0,D1}/<name>.c
                           the functions changed U0->U1 and D0->D1, cut from
                           the file text unchanged
    debian.patch           this patch, as fetched (sha256 checked)
    manifest.json          versions, commits, sha256, files, functions, verdict

If a patch in the series does not apply to the target file, the verdict is
'パッチが当たらない' and the case stops there. Nothing in the fetched data is
executed; `patch` runs from this process with explicit -d/-i paths.

Usage:
    python3 detect.py debian/trixie st.json --dry-run | python3 build.py <out> [--cache DIR]
"""
import difflib
import hashlib
import json
import re
import subprocess
import sys
import tempfile
import urllib.error
import urllib.request
from dataclasses import asdict, dataclass
from pathlib import Path

GITHUB_API = 'https://api.github.com/'
GITHUB_COMMIT = GITHUB_API + 'repos/curl/curl/commits/{sha}'
GITHUB_RAW = 'https://raw.githubusercontent.com/curl/curl/{ref}/{path}'
SALSA_RAW = 'https://salsa.debian.org/debian/curl/-/raw/{commit}/{path}'
NOT_APPLIED = 'パッチが当たらない'
# dpkg-source applies quilt patches without fuzz; offsets are allowed.
PATCH_CMD = ['patch', '-p1', '-F', '0', '-N', '-f', '--no-backup-if-mismatch']


def gh_api(url: str) -> bytes:
    """The unauthenticated API limit is 60 requests an hour per address; when
    it is exhausted, ask the gh CLI, which uses the caller's own login."""
    res = subprocess.run(['gh', 'api', url.removeprefix(GITHUB_API)],
                         capture_output=True, check=False)
    if res.returncode != 0:
        raise RuntimeError(f'gh api failed for {url}: {res.stderr.decode(errors="replace")}')
    return res.stdout


class Fetcher:
    """urllib with an on-disk cache. Contents are data only, never executed."""

    def __init__(self, cache: Path | None) -> None:
        self.cache = cache

    def get(self, url: str) -> bytes | None:
        """The body, or None on 404."""
        key = hashlib.sha256(url.encode()).hexdigest()
        if self.cache:
            hit = self.cache / key
            if hit.exists():
                return hit.read_bytes()
            if (self.cache / (key + '.404')).exists():
                return None
        req = urllib.request.Request(url, headers={'User-Agent': 'backport-proof'})
        try:
            with urllib.request.urlopen(req, timeout=60) as resp:
                body = resp.read()
        except urllib.error.HTTPError as e:
            if e.code == 403 and url.startswith(GITHUB_API):
                body = gh_api(url)
            elif e.code == 404:
                if self.cache:
                    (self.cache / (key + '.404')).write_bytes(b'')
                return None
            else:
                raise
        if self.cache:
            (self.cache / key).write_bytes(body)
        return body

    def need(self, url: str) -> bytes:
        body = self.get(url)
        if body is None:
            raise RuntimeError(f'not found: {url}')
        return body


def sha256(data: bytes | str) -> str:
    return hashlib.sha256(data.encode() if isinstance(data, str) else data).hexdigest()


def is_c_source(path: str) -> bool:
    return path.endswith(('.c', '.h')) and not path.startswith(('tests/', 'docs/'))


# --- C functions -----------------------------------------------------------

@dataclass(frozen=True)
class Func:
    name: str
    start: int  # first header line (0-based)
    end: int    # line of the closing `}` (inclusive)


NAME_RE = re.compile(r'([A-Za-z_]\w*)\s*\(')


def mask_comments(src: str) -> str:
    """src with every comment replaced by spaces (newlines kept), so line
    numbers stay the same. String and character literals are skipped, so a
    "*/*" inside a string does not open a comment."""
    out: list[str] = []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if c in '"\'':
            j = i + 1
            while j < n and src[j] != c and src[j] != '\n':
                j += 2 if src[j] == '\\' else 1
            out.append(src[i:j + 1])
            i = j + 1
        elif src.startswith('/*', i):
            j = src.find('*/', i + 2)
            j = n if j < 0 else j + 2
            out.append(re.sub(r'[^\n]', ' ', src[i:j]))
            i = j
        elif src.startswith('//', i):
            j = src.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i))
            i = j
        else:
            out.append(c)
            i += 1
    return ''.join(out)


def header_start(code: list[str], brace: int) -> int:
    """First line of the declaration ending just above the `{` line, on
    comment-masked lines. Walks back through the parameter list (which may
    hold comment-only lines), then over the return type, which in 8.14.1 and
    older is often on its own line."""
    j = brace - 1
    # lines between `)` and `{` that hold only a comment or a preprocessor
    # directive (`bool secure) /* TRUE if ...` continued, `#ifdef USE_X`)
    while j > 0 and (not code[j].strip() or code[j].lstrip().startswith('#')):
        j -= 1
    depth = 0
    while j >= 0:
        depth += code[j].count(')') - code[j].count('(')
        if depth <= 0:
            break
        j -= 1
    while j - 1 >= 0:
        s = code[j - 1].strip()
        if not s or s.startswith('#') or s.endswith((';', '}', '{', ')', ',')):
            break
        j -= 1
    return max(j, 0)


def functions(src: str) -> list[Func]:
    """Top-level function definitions, by curl's layout: the body opens with a
    line that is exactly `{` and closes with the next line that is exactly `}`."""
    lines = src.split('\n')
    code = mask_comments(src).split('\n')
    out: list[Func] = []
    i = 0
    while i < len(lines):
        if lines[i] != '{':
            i += 1
            continue
        start = header_start(code, i)
        m = NAME_RE.search(' '.join(code[start:i]))
        end = next((k for k in range(i + 1, len(lines)) if lines[k] == '}'), None)
        if m is None or end is None:
            i += 1
            continue
        out.append(Func(m.group(1), start, end))
        i = end + 1
    return out


def body(src: str, f: Func) -> str:
    return '\n'.join(src.split('\n')[f.start:f.end + 1]) + '\n'


def touches(f: Func, a: int, b: int) -> bool:
    """Lines [a, b) overlap f; an empty range is an insertion before line a."""
    if a == b:
        return f.start < a <= f.end
    return a <= f.end and f.start < b


def changed_functions(old: str, new: str) -> tuple[list[str], int]:
    """Names of functions touched by the line diff old->new, in order of first
    appearance, and the number of diff blocks outside any function."""
    fo, fn = functions(old), functions(new)
    names: list[str] = []
    outside = 0
    matcher = difflib.SequenceMatcher(None, old.split('\n'), new.split('\n'), autojunk=False)
    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag == 'equal':
            continue
        hit = [f.name for f in fo if touches(f, i1, i2)] + [f.name for f in fn if touches(f, j1, j2)]
        if not hit:
            outside += 1
        names += [n for n in dict.fromkeys(hit) if n not in names]
    return names, outside


# --- Debian ----------------------------------------------------------------

def base_tag(changelog: str) -> tuple[str, str]:
    """Debian version from the first changelog line, and the curl tag."""
    m = re.match(r'\S+ \(([^)]+)\)', changelog)
    if m is None:
        raise RuntimeError('cannot read debian/changelog')
    debver = m.group(1)
    upver = debver.split(':', 1)[-1].rsplit('-', 1)[0]
    upver = re.split(r'[+~]', upver)[0]
    if not re.fullmatch(r'\d+(\.\d+)+', upver):
        raise RuntimeError(f'unexpected upstream version: {debver}')
    return debver, 'curl-' + upver.replace('.', '_')


def series(text: str) -> list[str]:
    out: list[str] = []
    for line in text.splitlines():
        line = line.split('#', 1)[0].strip()
        if line:
            out.append(line.split()[0])
    return out


def strip1(path: str) -> str:
    path = path.split('\t')[0].strip()
    return path.split('/', 1)[1] if '/' in path else path


def patch_paths(patch: str) -> list[str]:
    """Files a patch touches, with -p1 applied the way quilt applies it
    (a/lib/x.c and pkg/lib/x.c both become lib/x.c)."""
    lines = patch.splitlines()
    out: list[str] = []
    for k, line in enumerate(lines[:-1]):
        if line.startswith('--- ') and lines[k + 1].startswith('+++ '):
            new, old = lines[k + 1][4:], line[4:]
            path = strip1(old if new.startswith('/dev/null') else new)
            if path not in out:
                out.append(path)
    return out


def sections_for(patch: str, target: str) -> str:
    """The `---`/`+++` sections of a patch that touch the target file (-p1)."""
    lines = patch.splitlines(keepends=True)
    keep: list[str] = []
    on = False
    for k, line in enumerate(lines):
        if line.startswith('--- ') and k + 1 < len(lines) and lines[k + 1].startswith('+++ '):
            new, old = lines[k + 1][4:], line[4:]
            path = strip1(old if new.startswith('/dev/null') else new)
            on = path == target
        elif line.startswith(('diff ', 'Index: ')):
            on = False
        if on:
            keep.append(line)
    return ''.join(keep)


def apply(src: str, target: str, part: str) -> tuple[str | None, str]:
    """Apply a patch section to src. (new text, '') or (None, patch output)."""
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp) / 'tree'
        dest = root / target
        dest.parent.mkdir(parents=True)
        dest.write_text(src)
        pfile = Path(tmp) / 'in.patch'
        pfile.write_text(part)
        res = subprocess.run(PATCH_CMD + ['-d', str(root), '-i', str(pfile),
                                          '-r', str(Path(tmp) / 'rej')],
                             cwd=tmp, capture_output=True, text=True)
        if res.returncode != 0:
            return None, res.stdout + res.stderr
        return dest.read_text(), ''


# --- one finding -----------------------------------------------------------

@dataclass
class Result:
    patch: str
    cve: str
    branch: str
    debian_commit: str
    verdict: str | None
    detail: str = ''
    debian_version: str | None = None
    base_tag: str | None = None
    upstream_fixed: str | None = None
    upstream_parent: str | None = None
    debian_patch_sha256: str | None = None
    target_file: str | None = None
    series_applied: list[dict] | None = None
    files: dict | None = None
    functions: dict | None = None
    changes_outside_functions: dict | None = None


def upstream(net: Fetcher, fixed: str) -> tuple[str, dict[str, str | None], dict[str, str | None]]:
    meta = json.loads(net.need(GITHUB_COMMIT.format(sha=fixed)))
    parent = meta['parents'][0]['sha']
    paths = [f['filename'] for f in meta['files'] if is_c_source(f['filename'])]
    u0: dict[str, str | None] = {}
    u1: dict[str, str | None] = {}
    for p in paths:
        b0 = net.get(GITHUB_RAW.format(ref=parent, path=p))
        b1 = net.get(GITHUB_RAW.format(ref=fixed, path=p))
        u0[p] = b0.decode('utf-8', 'replace') if b0 is not None else None
        u1[p] = b1.decode('utf-8', 'replace') if b1 is not None else None
    return parent, u0, u1


def debian(net: Fetcher, f: dict, target: str, res: Result) -> tuple[str, str] | None:
    """D0 and D1 text of the target file, or None with res.verdict set."""
    commit = f['commit']
    raw = lambda p: net.need(SALSA_RAW.format(commit=commit, path=p))
    res.debian_version, res.base_tag = base_tag(raw('debian/changelog').decode())
    names = series(raw('debian/patches/series').decode())
    if f['patch'] not in names:
        raise RuntimeError(f"{f['patch']} not in series")
    text = net.need(GITHUB_RAW.format(ref=res.base_tag, path=target)).decode()
    res.series_applied = []
    d0 = text
    for name in names[:names.index(f['patch']) + 1]:
        body_ = raw('debian/patches/' + name)
        part = sections_for(body_.decode('utf-8', 'replace'), target)
        if name == f['patch']:
            res.debian_patch_sha256 = sha256(body_)
            if res.debian_patch_sha256 != f['sha256']:
                raise RuntimeError(f"{name}: sha256 differs from detect.py's")
            d0 = text
        if not part:
            continue
        res.series_applied.append({'patch': name, 'sha256': sha256(body_)})
        new, log = apply(text, target, part)
        if new is None:
            res.verdict, res.detail = NOT_APPLIED, f'{name} on {target}:\n{log}'
            return None
        text = new
    return d0, text


def write(base: Path, role: str, path: str, text: str | None) -> str | None:
    if text is None:
        return None
    dest = base / role / path
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(text)
    return sha256(text)


def cut_all(base: Path, side: dict[str, dict[str, str | None]], names: list[str]) -> None:
    for role, files in side.items():
        for text in files.values():
            if text is None:
                continue
            for fn in functions(text):
                if fn.name in names:
                    dest = base / 'functions' / role / f'{fn.name}.c'
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    if not dest.exists():
                        dest.write_text(body(text, fn))


def side_changes(before: dict[str, str | None], after: dict[str, str | None]) -> tuple[list[dict], int]:
    names: list[str] = []
    outside = 0
    for p in before:
        n, o = changed_functions(before[p] or '', after[p] or '')
        names += [x for x in n if x not in names]
        outside += o
    present = lambda files, n: any(n in {f.name for f in functions(t)} for t in files.values() if t)
    return [{'name': n, 'before': present(before, n), 'after': present(after, n)} for n in names], outside


def build(net: Fetcher, f: dict, out: Path) -> Result:
    res = Result(f['patch'], f['cve'], f['branch'], f['commit'], f['verdict'],
                 upstream_fixed=f['upstream_fixed'])
    base = out / f['patch'].removesuffix('.patch')
    base.mkdir(parents=True, exist_ok=True)
    if res.verdict is None:
        build_open(net, f, res, base)
    (base / 'manifest.json').write_text(json.dumps(asdict(res), ensure_ascii=False, indent=1) + '\n')
    return res


def build_open(net: Fetcher, f: dict, res: Result, base: Path) -> None:
    text = net.need(SALSA_RAW.format(commit=f['commit'], path='debian/patches/' + f['patch']))
    (base / 'debian.patch').write_bytes(text)
    # detect.py strips only a/ and b/; quilt patches in older branches use pkg/lib/x.c
    targets = [p for p in patch_paths(text.decode('utf-8', 'replace'))
               if p.endswith('.c') and is_c_source(p)]
    if len(targets) != 1:
        raise RuntimeError(f"{f['patch']}: expected one .c file, found {targets}")
    res.target_file = target = targets[0]
    if [target] != list(f['c_files']):
        res.detail = f"detect.py reported c_files {f['c_files']}; read from the patch: {target}"
    dd = debian(net, f, target, res)
    if dd is None:
        return
    parent, u0, u1 = upstream(net, f['upstream_fixed'])
    res.upstream_parent = parent
    d0, d1 = {target: dd[0]}, {target: dd[1]}
    res.files = {role: {p: write(base, role, p, t) for p, t in side.items()}
                 for role, side in (('U0', u0), ('U1', u1), ('D0', d0), ('D1', d1))}
    fu, ou = side_changes(u0, u1)
    fd, od = side_changes(d0, d1)
    res.functions = {'U': fu, 'D': fd}
    res.changes_outside_functions = {'U': ou, 'D': od}
    cut_all(base, {'U0': u0, 'U1': u1}, [x['name'] for x in fu])
    cut_all(base, {'D0': d0, 'D1': d1}, [x['name'] for x in fd])


def main() -> None:
    args = sys.argv[1:]
    cache = None
    if '--cache' in args:
        k = args.index('--cache')
        cache = Path(args[k + 1])
        cache.mkdir(parents=True, exist_ok=True)
        args = args[:k] + args[k + 2:]
    if len(args) != 1:
        sys.exit(__doc__)
    out = Path(args[0])
    net = Fetcher(cache)
    for raw in sys.stdin:
        if not raw.strip():
            continue
        f = json.loads(raw)
        try:
            res = build(net, f, out)
        except (RuntimeError, OSError, KeyError, ValueError) as e:
            print(json.dumps({'patch': f.get('patch'), 'error': str(e)}, ensure_ascii=False))
            continue
        fns = res.functions or {}
        print(json.dumps({'patch': res.patch, 'verdict': res.verdict,
                          'U': [x['name'] for x in fns.get('U', [])],
                          'D': [x['name'] for x in fns.get('D', [])]}, ensure_ascii=False))


if __name__ == '__main__':
    main()
