#!/usr/bin/env python3
"""CVE-2026-3805（research/backport-proof-debian/cases/CVE-2026-3805.md）の翻訳単位を作る。

4つの翻訳単位（関数 smb_parse_url_path）:
  deb2026_3805_up_after.c   上流の修正後  e090be9f73a7a71459ef678c7cc4b1f75e3ea883（U1）
  deb2026_3805_up_before.c  上流の修正前  22b0cbe65f6738bdf002f0331895aba52ae0633e（U0、修正の親）
  deb2026_3805_deb_after.c  curl 8.14.1 に Debian の CVE-2026-3805.patch を `patch` でそのまま当てたもの（D1）
  deb2026_3805_deb_before.c curl 8.14.1（D0）

関数の本体は原文から機械で切り出す。前置き（prelude.h）だけが手で用意した部分である。
使い方: python3 extract.py   （gh api と salsa.debian.org の raw URL で取得する）
"""
import hashlib
import re
import subprocess
import sys
import tempfile
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = "lib/smb.c"
FUNCS = ["smb_parse_url_path"]
UP_AFTER = "e090be9f73a7a71459ef678c7cc4b1f75e3ea883"
UP_BEFORE = "22b0cbe65f6738bdf002f0331895aba52ae0633e"
OLD = "curl-8_14_1"
DEBIAN_COMMIT = "c2a97b9ea54e3ad6c4381c87a0ef235af2917863"  # salsa debian/curl の debian/trixie（8.14.1-2+deb13u6）
DEBIAN_PATCH = (f"https://salsa.debian.org/debian/curl/-/raw/{DEBIAN_COMMIT}"
                "/debian/patches/CVE-2026-3805.patch")
DEBIAN_PATCH_SHA256 = "3f1728d41f0e51aeb84324660c817a5bc7a856aa919831d406e1a371bb2d1116"


def gh_raw(path: str, ref: str) -> str:
    out = subprocess.run(
        ["gh", "api", "-H", "Accept: application/vnd.github.raw",
         f"repos/curl/curl/contents/{path}?ref={ref}"],
        check=True, capture_output=True, text=True)
    return out.stdout


def fetch_debian_patch() -> str:
    with urllib.request.urlopen(DEBIAN_PATCH, timeout=30) as r:
        body = r.read()
    digest = hashlib.sha256(body).hexdigest()
    if digest != DEBIAN_PATCH_SHA256:
        sys.exit(f"Debian patch sha256 mismatch: {digest}")
    return body.decode()


def apply_patch(src: str, patch_text: str) -> str:
    """patch -p1 で当てる。当たらない hunk があれば止める（手では直さない）。"""
    with tempfile.TemporaryDirectory() as d:
        target = Path(d) / SRC
        target.parent.mkdir(parents=True)
        target.write_text(src)
        res = subprocess.run(["patch", "-p1", "--no-backup-if-mismatch"], cwd=d,
                             input=patch_text, capture_output=True, text=True)
        if res.returncode != 0:
            sys.exit(f"Debian patch did not apply:\n{res.stdout}{res.stderr}")
        return target.read_text()


def cut_function(src: str, name: str) -> str:
    """行頭の戻り値の型から始まり、行頭の `}` で終わる範囲を返す。前方宣言（`;` で終わる）は飛ばす。"""
    for m in re.finditer(rf"^[A-Za-z_][^\n;]*\b{name}\(", src, re.MULTILINE):
        body = src.find("\n{\n", m.start())
        if body < 0 or ";" in src[m.start():body]:
            continue
        end = src.find("\n}\n", body)
        if end < 0:
            sys.exit(f"end of function not found: {name}")
        return src[m.start():end + 2]
    sys.exit(f"function not found: {name}")


def unit(src: str, label: str) -> str:
    bodies = [cut_function(src, f) for f in FUNCS]
    header = (f"/* curl {SRC} ({label})\n"
              f" * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */\n"
              f'#include "prelude.h"\n\n')
    return header + "\n".join(bodies) + '\n#include "epilogue.h"\n'


def main() -> None:
    old = gh_raw(SRC, OLD)
    patch_text = fetch_debian_patch()
    (HERE / "debian.patch").write_text(patch_text)
    (HERE / "deb2026_3805_up_after.c").write_text(unit(gh_raw(SRC, UP_AFTER), f"@ {UP_AFTER}、上流の修正後"))
    (HERE / "deb2026_3805_up_before.c").write_text(unit(gh_raw(SRC, UP_BEFORE), f"@ {UP_BEFORE}、上流の修正前"))
    (HERE / "deb2026_3805_deb_after.c").write_text(
        unit(apply_patch(old, patch_text), f"@ {OLD} に Debian の CVE-2026-3805.patch を当てた後"))
    (HERE / "deb2026_3805_deb_before.c").write_text(unit(old, f"@ {OLD}、修正前"))
    print("wrote debian.patch deb2026_3805_{up,deb}_{after,before}.c")


if __name__ == "__main__":
    main()
