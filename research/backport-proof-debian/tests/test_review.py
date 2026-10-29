"""PROTOCOL-auto §3.9: a second agent reads the stated properties, blind to the result."""
import json
import sys
from pathlib import Path

import review

NOTES = '# CVE-1\n## 性質\nP1: no leak\n## 結果\n**成功**\n### 読み方\nmore\n'
MANIFEST = {'patch': 'CVE-1.patch', 'branch': 'debian/bookworm', 'cve': 'CVE-1', 'upstream_fixed': 'a' * 40}


def answer(**bad: str) -> dict:
    out = {q: {'ok': q not in bad, 'reason': bad.get(q, 'fine')} for q in review.QUESTIONS}
    return {**out, 'summary': 'P1 says no leak.'}


def test_the_reader_does_not_see_the_result() -> None:
    text = review.statement(NOTES)
    assert 'P1: no leak' in text and '成功' not in text and '結果' not in text


def test_notes_without_a_results_section_are_given_whole() -> None:
    assert review.statement('# x\n## 性質\np\n') == '# x\n## 性質\np\n'


def test_prompt_fills_every_placeholder(tmp_path: Path) -> None:
    text = review.render(MANIFEST, tmp_path / 's.md', tmp_path / 'in')
    assert '$' not in text and 'https://curl.se/docs/CVE-1.html' in text


def test_parse_reads_the_structured_output() -> None:
    assert review.parse(json.dumps({'structured_output': answer()})) == answer()
    assert review.parse(json.dumps({'result': json.dumps(answer())})) == answer()


def test_parse_rejects_incomplete_answers() -> None:
    partial = answer()
    del partial['p0_states_bug']
    for stdout in ('not json', json.dumps({'result': 'prose'}), json.dumps({'structured_output': partial})):
        assert review.parse(stdout) is None


def test_summary_lists_the_problems() -> None:
    s = review.summarize(answer(scope_keeps_the_path='the premise excludes the redirect'))
    assert s['status'] == '指摘あり' and s['problems'] == ['scope_keeps_the_path']
    assert review.summarize(answer())['status'] == '指摘なし'
    assert review.summarize(None, 'exit 1')['status'] == '読み直しできず'


def test_review_runs_the_reader_on_the_cut_notes(tmp_path: Path) -> None:
    notes = tmp_path / 'CVE-1.md'
    notes.write_text(NOTES)
    seen = tmp_path / 'seen.txt'
    # a stand-in reader: records the statement file it was pointed at, then answers
    reader = tmp_path / 'reader.py'
    reader.write_text(
        'import sys, json, re\n'
        'prompt = sys.stdin.read()\n'
        'path = re.search(r"`([^`]*CVE-1.md)`", prompt).group(1)\n'
        f'open({str(seen)!r}, "w").write(open(path).read())\n'
        f'print(json.dumps({{"structured_output": json.loads({json.dumps(answer())!r})}}))\n')
    out = review.review(notes, tmp_path, MANIFEST, cmd=[sys.executable, str(reader)])
    assert out['status'] == '指摘なし'
    assert '成功' not in seen.read_text() and 'P1: no leak' in seen.read_text()
