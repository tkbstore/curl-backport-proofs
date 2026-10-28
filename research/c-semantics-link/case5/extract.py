#!/usr/bin/env python3
"""Case 5 の翻訳単位を、curl のソースから関数の本体をそのまま切り出して作る。

PROTOCOL §4「関数の本体は変えない」を手で守らないために、本体は文字列として複製するだけにする。
前置き（prelude.h）だけが手で書いた部分である。

使い方: python3 extract.py   （gh api で curl のソースを取得する。git の作業ツリーは使わない）
"""
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIX = "72352daba01ba8072b6c1c0254cb77860ed1ab06"
PARENT = "bdda3a268f0fd1a1bb4b16b9322aa6bc055b8e76"
# 同じ翻訳単位に入れる関数（url.c 内での出現順に並べる）
FUNCS = ["get_protocol_family", "url_match_ssl_use", "url_match_ssl_config"]


def fetch_url_c(ref: str) -> str:
    out = subprocess.run(
        ["gh", "api", "-H", "Accept: application/vnd.github.raw",
         f"repos/curl/curl/contents/lib/url.c?ref={ref}"],
        check=True, capture_output=True, text=True)
    return out.stdout


def cut_function(src: str, name: str) -> str:
    """`static <型> name(` で始まり、行頭の `}` で終わる範囲を返す。"""
    m = re.search(rf"^static [^\n;]*\b{name}\(", src, re.MULTILINE)
    if m is None:
        sys.exit(f"function not found: {name}")
    end = src.find("\n}\n", m.start())
    if end < 0:
        sys.exit(f"end of function not found: {name}")
    return src[m.start():end + 2]


def build(ref: str, label: str) -> str:
    src = fetch_url_c(ref)
    bodies = [cut_function(src, f) for f in FUNCS]
    header = (f"/* curl lib/url.c @ {ref} ({label})\n"
              f" * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */\n"
              f'#include "prelude.h"\n\n')
    return header + "\n".join(bodies) + '\n#include "epilogue.h"\n'


def main() -> None:
    for ref, label, out in [(FIX, "修正後", "case5_after.c"),
                            (PARENT, "修正前", "case5_before.c")]:
        (HERE / out).write_text(build(ref, label))
        print(f"wrote {out}")


if __name__ == "__main__":
    main()
