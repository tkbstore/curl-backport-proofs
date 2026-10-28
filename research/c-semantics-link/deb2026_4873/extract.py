#!/usr/bin/env python3
"""CVE-2026-4873 の4つの翻訳単位を作る（research/backport-proof-debian/PROTOCOL-trixie-batch.md §3）。

- U1: 上流の修正後（curl 507e7be573b0a76fca597b75ff7cb27a66e7d865）
- U0: 上流の修正前（その親 62d77b12fce55d3481bb0b2e70e0f921c8cbfe5e）
- D0: curl 8.14.1 に、Debian の series で対象のパッチより前にある lib/url.c のパッチをすべて当てたもの
- D1: D0 に Debian の CVE-2026-4873.patch を当てたもの

Debian のパッチは series の順に積み重なっていて、対象のパッチは素の 8.14.1 には当たらない（文脈が前のパッチに依存する）。
そのため D0 を「Debian が出荷した、このパッチを当てる直前の状態」とした。パッチは `patch` でそのまま当て、手では直さない。
各パッチの lib/url.c 以外のファイル（テスト・文書）の部分は当てない。

関数の本体は原文から文字列として切り出す。手で用意したのは前置き（U は prelude_u.h、D は prelude_d.h）と末尾（epilogue.h）だけ。
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
NAME = "deb2026_4873"
SRC = "lib/url.c"
FIX = "507e7be573b0a76fca597b75ff7cb27a66e7d865"
PARENT = "62d77b12fce55d3481bb0b2e70e0f921c8cbfe5e"
OLD = "curl-8_14_1"
FUNCS = ["get_protocol_family", "url_match_ssl_use"]
DEBIAN_COMMIT = "c2a97b9ea54e3ad6c4381c87a0ef235af2917863"  # salsa debian/curl の debian/trixie（8.14.1-2+deb13u6）
# series の順。最後が対象のパッチ。sha256 は取得のたびに照合する
PATCHES = [
    ("CVE-2026-1965_1", "9aaf4c3eb03649c54e8f8cfbd0a28c5ea786550c06aaeb573109c010d98be65c"),
    ("CVE-2026-1965_2", "157bb9a263134dda41945a6ba5398ee274ab3c251a1da611689e407aceda66b9"),
    ("CVE-2026-3784", "7bec4e76f12b6fa45b4c96f238fa35fc6efe83afa2f9c70e52f613d164a40bf1"),
    ("CVE-2026-4873", "e7a537702e76a3e9a6fb3eb2954a02da63c8e75bc7bd81a77b59e379364c0a56"),
]


def gh_raw(ref: str) -> str:
    out = subprocess.run(
        ["gh", "api", "-H", "Accept: application/vnd.github.raw",
         f"repos/curl/curl/contents/{SRC}?ref={ref}"],
        check=True, capture_output=True, text=True)
    return out.stdout


def fetch_debian_patch(name: str, sha: str) -> str:
    url = f"https://salsa.debian.org/debian/curl/-/raw/{DEBIAN_COMMIT}/debian/patches/{name}.patch"
    with urllib.request.urlopen(url, timeout=30) as r:
        body = r.read()
    digest = hashlib.sha256(body).hexdigest()
    if digest != sha:
        sys.exit(f"Debian patch sha256 mismatch: {name} {digest}")
    return body.decode()


def only_src(patch_text: str) -> str:
    """パッチから lib/url.c の部分だけを取り出す（中身は変えない）。"""
    parts = re.split(r"(?m)^(?=diff --git )", patch_text)
    keep = [p for p in parts if p.startswith(f"diff --git a/{SRC} ")]
    if not keep:
        sys.exit(f"no {SRC} section in patch")
    return "".join(keep)


def apply_patch(src: str, patch_text: str, name: str) -> str:
    """patch -p1 で当てる。当たらない hunk があれば止める（手では直さない）。"""
    with tempfile.TemporaryDirectory() as d:
        target = Path(d) / SRC
        target.parent.mkdir(parents=True)
        target.write_text(src)
        res = subprocess.run(["patch", "-p1", "--no-backup-if-mismatch"], cwd=d,
                             input=only_src(patch_text), capture_output=True, text=True)
        if res.returncode != 0:
            sys.exit(f"Debian patch {name} did not apply:\n{res.stdout}{res.stderr}")
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


def unit(src: str, label: str, prelude: str) -> str:
    bodies = [cut_function(src, f) for f in FUNCS]
    header = (f"/* curl {SRC} @ {label}\n"
              f" * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */\n"
              f'#include "{prelude}"\n\n')
    return header + "\n".join(bodies) + '\n#include "epilogue.h"\n'


def main() -> None:
    old = gh_raw(OLD)
    d0 = old
    texts = []
    for pname, sha in PATCHES:
        text = fetch_debian_patch(pname, sha)
        texts.append((pname, text))
    for pname, text in texts[:-1]:
        d0 = apply_patch(d0, text, pname)
    tname, ttext = texts[-1]
    d1 = apply_patch(d0, ttext, tname)
    (HERE / "debian.patch").write_text(ttext)
    pre = ", ".join(p for p, _ in texts[:-1]) or "なし"
    outs = [
        (f"{NAME}_u1.c", gh_raw(FIX), f"{FIX}（上流の修正後 U1）"),
        (f"{NAME}_u0.c", gh_raw(PARENT), f"{PARENT}（上流の修正前 U0）"),
        (f"{NAME}_d1.c", d1, f"{OLD} + Debian {pre}, {tname}（D1）"),
        (f"{NAME}_d0.c", d0, f"{OLD} + Debian {pre}（D0）"),
    ]
    for fname, src, label in outs:
        # 上流は struct Curl_scheme（conn->scheme）、8.14.1 は struct Curl_handler（conn->handler）なので前置きを分ける
        prelude = "prelude_u.h" if fname.endswith(("_u1.c", "_u0.c")) else "prelude_d.h"
        (HERE / fname).write_text(unit(src, label, prelude))
        print(f"wrote {fname}")


if __name__ == "__main__":
    main()
