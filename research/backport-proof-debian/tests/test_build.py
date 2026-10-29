"""PROTOCOL-auto §3.3: the four C sources and the changed functions."""
import pytest

import build

SRC = '''/* a comment with { and } */
static int
helper(int a, /* the input */
       int b)
{
  const char *s = "/* not a comment {";
  return a + b;
}

int Curl_thing(void)
{
  return helper(1, 2);
}
'''


def test_functions_follow_curls_layout() -> None:
    fs = build.functions(SRC)
    assert [(f.name, f.start, f.end) for f in fs] == [('helper', 1, 7), ('Curl_thing', 9, 12)]


def test_body_is_the_original_text() -> None:
    f = build.functions(SRC)[1]
    assert build.body(SRC, f) == 'int Curl_thing(void)\n{\n  return helper(1, 2);\n}\n'


def test_mask_comments_keeps_line_numbers_and_strings() -> None:
    masked = build.mask_comments(SRC)
    assert masked.count('\n') == SRC.count('\n')
    assert '"/* not a comment {"' in masked
    assert 'the input' not in masked


def test_changed_functions_names_only_the_changed_body() -> None:
    new = SRC.replace('return a + b;', 'return a - b;')
    assert build.changed_functions(SRC, new) == (['helper'], 0)


def test_a_change_between_functions_is_outside() -> None:
    new = SRC.replace('}\n\nint Curl_thing', '}\n\n#define X 1\n\nint Curl_thing')
    assert build.changed_functions(SRC, new) == ([], 1)


@pytest.mark.parametrize('first_line,expected', [
    ('curl (8.14.1-2+deb13u6) trixie-security; urgency=medium', ('8.14.1-2+deb13u6', 'curl-8_14_1')),
    ('curl (7.88.1-10+deb12u15) bookworm; urgency=medium', ('7.88.1-10+deb12u15', 'curl-7_88_1')),
    ('curl (1:8.0.0~rc1-1) unstable; urgency=low', ('1:8.0.0~rc1-1', 'curl-8_0_0')),
])
def test_base_tag(first_line: str, expected: tuple[str, str]) -> None:
    assert build.base_tag(first_line + '\n') == expected


def test_base_tag_rejects_garbage() -> None:
    with pytest.raises(RuntimeError):
        build.base_tag('not a changelog\n')


def test_series_drops_comments_and_options() -> None:
    text = '# header\nfix-a.patch\n\nCVE-1.patch -p1\nCVE-2.patch # why\n'
    assert build.series(text) == ['fix-a.patch', 'CVE-1.patch', 'CVE-2.patch']


PATCH = '''Subject: two files
--- curl.orig/lib/url.c
+++ curl/lib/url.c
@@ -1,3 +1,3 @@
 a
-b
+B
 c
--- /dev/null
+++ b/lib/new.c
@@ -0,0 +1 @@
+x
'''


def test_patch_paths_apply_p1_like_quilt() -> None:
    assert build.patch_paths(PATCH) == ['lib/url.c', 'lib/new.c']


def test_sections_for_keeps_only_the_target() -> None:
    part = build.sections_for(PATCH, 'lib/url.c')
    assert '+B' in part and 'new.c' not in part


def test_apply_allows_offsets() -> None:
    part = build.sections_for(PATCH, 'lib/url.c')
    new, err = build.apply('top\nmore\na\nb\nc\n', 'lib/url.c', part)
    assert err == '' and new == 'top\nmore\na\nB\nc\n'


def test_apply_refuses_fuzz() -> None:
    """dpkg-source applies without fuzz, so a changed context line is a failure."""
    part = build.sections_for(PATCH, 'lib/url.c')
    new, err = build.apply('a\nb\nC\n', 'lib/url.c', part)
    assert new is None and err


# --- §3.3 D0 / D1 from Debian's series ---------------------------------------

def hunk(path: str, old: str, new: str) -> str:
    return f'--- a/{path}\n+++ b/{path}\n@@ -1,3 +1,3 @@\n {old[0]}\n-{old[1]}\n+{new}\n {old[2]}\n'


class FakeNet:
    """build.Fetcher with a fixed set of URLs."""

    def __init__(self, files: dict[str, bytes]) -> None:
        self.files = files

    def need(self, url: str) -> bytes:
        return self.files[url]


def debian_case(p2: str, sha: str | None = None) -> tuple[FakeNet, dict]:
    salsa = lambda p: build.SALSA_RAW.format(commit='C', path=p)
    p1 = hunk('lib/url.c', 'abc', 'B')               # earlier patch on the same file
    other = hunk('lib/http.c', 'xyz', 'Y')           # touches another file only
    p3 = hunk('lib/url.c', 'aBc', 'Z')               # later patch: must not be applied
    files = {salsa('debian/changelog'): b'curl (8.14.1-2+deb13u6) trixie; urgency=medium\n',
             salsa('debian/patches/series'): b'p1.patch\nother.patch\nCVE-1.patch\np3.patch\n',
             salsa('debian/patches/p1.patch'): p1.encode(),
             salsa('debian/patches/other.patch'): other.encode(),
             salsa('debian/patches/CVE-1.patch'): p2.encode(),
             salsa('debian/patches/p3.patch'): p3.encode(),
             build.GITHUB_RAW.format(ref='curl-8_14_1', path='lib/url.c'): b'a\nb\nc\n'}
    f = {'commit': 'C', 'patch': 'CVE-1.patch', 'sha256': sha or build.sha256(p2)}
    return FakeNet(files), f


def result() -> build.Result:
    return build.Result('CVE-1.patch', 'CVE-1', 'debian/trixie', 'C', None)


def test_d0_is_just_before_this_patch_and_d1_includes_it() -> None:
    net, f = debian_case(hunk('lib/url.c', 'aBc', 'Q'))
    res = result()
    assert build.debian(net, f, 'lib/url.c', res) == ('a\nB\nc\n', 'a\nQ\nc\n')
    assert res.base_tag == 'curl-8_14_1'
    assert [x['patch'] for x in res.series_applied] == ['p1.patch', 'CVE-1.patch']


def test_a_patch_that_does_not_apply_is_a_verdict() -> None:
    net, f = debian_case(hunk('lib/url.c', 'axc', 'Q'))
    res = result()
    assert build.debian(net, f, 'lib/url.c', res) is None
    assert res.verdict == build.NOT_APPLIED and 'CVE-1.patch' in res.detail


def test_the_patch_must_be_the_one_detect_saw() -> None:
    net, f = debian_case(hunk('lib/url.c', 'aBc', 'Q'), sha='0' * 64)
    with pytest.raises(RuntimeError, match='sha256'):
        build.debian(net, f, 'lib/url.c', result())
