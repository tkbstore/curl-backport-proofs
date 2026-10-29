"""PROTOCOL-auto §2, §3.1, §3.2: detection and the size rule."""
import pytest

import detect

FIXED = 'a' * 40


def patch(*sections: tuple[str, int]) -> str:
    """A git-style patch with one hunk of n added lines per (path, n)."""
    out = ['From x Mon Sep 17 00:00:00 2001', 'Subject: [PATCH] fix', '']
    for path, n in sections:
        out += [f'diff --git a/{path} b/{path}', f'--- a/{path}', f'+++ b/{path}',
                f'@@ -1,1 +1,{n + 1} @@', ' context'] + [f'+line {k}' for k in range(n)]
    return '\n'.join(out) + '\n'


@pytest.mark.parametrize('path,expected', [
    ('a/lib/url.c', 'lib/url.c'), ('b/lib/url.c', 'lib/url.c'),
    ('curl/lib/url.c', 'lib/url.c'), ('curl.orig/lib/url.c', 'lib/url.c'),
    ('lib/url.c', 'lib/url.c'),
])
def test_strip_prefix(path: str, expected: str) -> None:
    assert detect.strip_prefix(path) == expected


def test_c_changes_counts_only_c_files_outside_tests_and_docs() -> None:
    text = patch(('lib/url.c', 3), ('lib/url.h', 5), ('tests/unit/u.c', 7), ('docs/x.c', 2))
    assert detect.c_changes(text) == (('lib/url.c',), 3)


def test_c_changes_counts_removed_lines() -> None:
    text = patch(('lib/url.c', 0)).replace(' context', '-old\n+new')
    assert detect.c_changes(text) == (('lib/url.c',), 2)


def test_c_changes_ignores_the_format_patch_trailer() -> None:
    """git format-patch ends with "-- " and the git version; neither is a change."""
    text = patch(('lib/url.c', 3)) + '-- \n2.39.2\n\n'
    assert detect.c_changes(text) == (('lib/url.c',), 3)


@pytest.mark.parametrize('name,cve', [
    ('CVE-2026-4873.patch', 'CVE-2026-4873'), ('CVE-2026-1965_2.patch', 'CVE-2026-1965'),
])
def test_patch_name(name: str, cve: str) -> None:
    assert detect.PATCH_RE.match(name).group(1) == cve


def test_patch_name_rejects_other_patches() -> None:
    assert detect.PATCH_RE.match('fix-build.patch') is None


def judge(monkeypatch: pytest.MonkeyPatch, text: str, fixed: list[str]) -> detect.Finding:
    monkeypatch.setattr(detect, 'upstream_fixed', lambda cve: fixed)
    return detect.judge('debian/trixie', 'c' * 40, 'CVE-2026-0001.patch', text.encode())


@pytest.mark.parametrize('fixed', [[], [FIXED, 'b' * 40]])
def test_upstream_fix_must_be_unique(monkeypatch: pytest.MonkeyPatch, fixed: list[str]) -> None:
    f = judge(monkeypatch, patch(('lib/url.c', 3)), fixed)
    assert f.verdict == '上流の修正を特定できない' and f.upstream_fixed is None


def test_no_c_change(monkeypatch: pytest.MonkeyPatch) -> None:
    assert judge(monkeypatch, patch(('docs/CURLOPT.md', 3)), [FIXED]).verdict == 'C の変更が無い'


@pytest.mark.parametrize('sections,verdict', [
    ((('lib/url.c', 40),), None),
    ((('lib/url.c', 41),), '対象外（大きさ）'),
    ((('lib/url.c', 2), ('lib/http.c', 2)), '対象外（大きさ）'),
])
def test_size_rule(monkeypatch: pytest.MonkeyPatch, sections: tuple, verdict: str | None) -> None:
    f = judge(monkeypatch, patch(*sections), [FIXED])
    assert f.verdict == verdict
    assert f.upstream_fixed == FIXED


def test_finding_records_the_sha256_of_the_patch(monkeypatch: pytest.MonkeyPatch) -> None:
    import hashlib
    text = patch(('lib/url.c', 1))
    assert judge(monkeypatch, text, [FIXED]).sha256 == hashlib.sha256(text.encode()).hexdigest()
