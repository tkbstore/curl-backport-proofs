"""The public copy: internal sections dropped, the Lean dependency made public."""
from pathlib import Path

import pytest

# publish/ is not part of the public copy (export.py leaves it out)
export = pytest.importorskip('export')


def test_strip_section_drops_up_to_the_next_heading_of_the_same_level(tmp_path: Path) -> None:
    doc = tmp_path / 'd.md'
    doc.write_text('# T\n## 1. keep\na\n## 7. internal\nsecret\n### sub\nmore\n## 8. keep too\nb\n')
    export.strip_section(doc, '## 7. internal')
    text = doc.read_text()
    assert 'secret' not in text and 'more' not in text
    assert '## 7. internal' in text and export.OMITTED in text
    assert '## 8. keep too\nb' in text and '## 1. keep\na' in text


def test_strip_section_fails_loudly_when_the_heading_moved(tmp_path: Path) -> None:
    doc = tmp_path / 'd.md'
    doc.write_text('# T\n')
    with pytest.raises(SystemExit):
        export.strip_section(doc, '## gone')


def test_lakefile_points_to_the_public_dependency(tmp_path: Path) -> None:
    path = tmp_path / export.LAKEFILE
    path.parent.mkdir(parents=True)
    path.write_text(f'[[require]]\nname = "clean"\n{export.LOCAL_REQUIRE}\n')
    export.point_lakefile_to_public(tmp_path)
    text = path.read_text()
    assert export.LOCAL_REQUIRE not in text and 'github.com/Certora/clean' in text


def test_the_real_documents_still_have_the_sections_export_strips() -> None:
    root = Path(__file__).resolve().parents[3]
    for rel, heading in export.STRIP:
        assert heading + '\n' in (root / rel).read_text(), rel
    assert export.LOCAL_REQUIRE in (root / export.LAKEFILE).read_text()
