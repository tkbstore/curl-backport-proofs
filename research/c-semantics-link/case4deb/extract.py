#!/usr/bin/env python3
"""Case 4 の Debian バックポート（research/backport-proof-debian/PROTOCOL.md）の翻訳単位を作る。

1. curl 8.14.1 の lib/vquic/vquic-tls.c を取得する（修正前）
2. Debian trixie の debian/patches/CVE-2025-13034.patch を `patch` でそのまま当てる（修正後）。手では直さない
3. 対象の関数の本体を切り出す。enum dupstring も 8.14.1 の lib/urldata.h から切り出す（enum.h）

前置き（prelude.h）だけが手で用意した部分である。
使い方: python3 extract.py   （gh api と salsa.debian.org の raw URL で取得する。git の作業ツリーは使わない）
"""
import hashlib
import re
import subprocess
import sys
import tempfile
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent
OLD = "curl-8_14_1"
SRC = "lib/vquic/vquic-tls.c"
FUNCS = ["Curl_vquic_tls_verify_peer"]
DEBIAN_COMMIT = "c2a97b9ea54e3ad6c4381c87a0ef235af2917863"  # salsa debian/curl の debian/trixie（8.14.1-2+deb13u6）
DEBIAN_PATCH = (f"https://salsa.debian.org/debian/curl/-/raw/{DEBIAN_COMMIT}"
                "/debian/patches/CVE-2025-13034.patch")
DEBIAN_PATCH_SHA256 = "6d3caaf6f401513058902f6ffcc011d0fe173ac61aca0cfe32bacbc9269b1e27"


def gh_raw(path: str) -> str:
    out = subprocess.run(
        ["gh", "api", "-H", "Accept: application/vnd.github.raw",
         f"repos/curl/curl/contents/{path}?ref={OLD}"],
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
    """行頭の戻り値の型から始まり、行頭の `}` で終わる範囲を返す。"""
    m = re.search(rf"^[A-Za-z_][^\n;]*\b{name}\(", src, re.MULTILINE)
    if m is None:
        sys.exit(f"function not found: {name}")
    end = src.find("\n}\n", m.start())
    if end < 0:
        sys.exit(f"end of function not found: {name}")
    return src[m.start():end + 2]


def cut_enum(src: str, name: str) -> str:
    m = re.search(rf"^enum {name} {{", src, re.MULTILINE)
    if m is None:
        sys.exit(f"enum not found: {name}")
    end = src.find("\n};\n", m.start())
    if end < 0:
        sys.exit(f"end of enum not found: {name}")
    return src[m.start():end + 4]


def unit(src: str, label: str) -> str:
    bodies = [cut_function(src, f) for f in FUNCS]
    header = (f"/* curl {SRC} @ {OLD} ({label})\n"
              f" * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */\n"
              f'#include "prelude.h"\n\n')
    return header + "\n".join(bodies)


def main() -> None:
    before = gh_raw(SRC)
    patch_text = fetch_debian_patch()
    after = apply_patch(before, patch_text)
    (HERE / "debian.patch").write_text(patch_text)
    (HERE / "case4deb_before.c").write_text(unit(before, "修正前"))
    (HERE / "case4deb_after.c").write_text(unit(after, "Debian の CVE-2025-13034.patch を当てた後"))
    (HERE / "enum.h").write_text(cut_enum(gh_raw("lib/urldata.h"), "dupstring"))
    print("wrote debian.patch case4deb_before.c case4deb_after.c enum.h")


if __name__ == "__main__":
    main()
