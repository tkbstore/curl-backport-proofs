#!/usr/bin/env python3
"""Case 1 の翻訳単位を、curl のソースから関数の本体をそのまま切り出して作る。

前置き（prelude.h）だけが手で用意した部分である。
`Curl_pp_readresp` は static でないので、CompCert は消さない（epilogue.h は要らない）。

使い方: python3 extract.py   （gh api で curl のソースを取得する。git の作業ツリーは使わない）
"""
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIX = "753735af87f5c30cb6f60a70342f8bc4bc5fd5db"
PARENT = "4a608405b6911e2fe374fca4239b3480a4e0cb2f"
SRC = "lib/pingpong.c"
# 同じ翻訳単位に入れる関数（pingpong.c 内での出現順に並べる）
FUNCS = ["pingpong_read", "Curl_pp_readresp"]


def fetch(ref: str) -> str:
    out = subprocess.run(
        ["gh", "api", "-H", "Accept: application/vnd.github.raw",
         f"repos/curl/curl/contents/{SRC}?ref={ref}"],
        check=True, capture_output=True, text=True)
    return out.stdout


def cut_function(src: str, name: str) -> str:
    """行頭の戻り値の型から始まり、行頭の `}` で終わる範囲を返す。"""
    m = re.search(rf"^[A-Za-z_][^\n;]*\b{name}\(", src, re.MULTILINE)
    if m is None:
        sys.exit(f"function not found: {name}")
    end = src.find("\n}\n", m.start())
    if end < 0:
        sys.exit(f"end of function not found: {name}")
    return src[m.start():end + 2]


def build(ref: str, label: str) -> str:
    src = fetch(ref)
    bodies = [cut_function(src, f) for f in FUNCS]
    header = (f"/* curl {SRC} @ {ref} ({label})\n"
              f" * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */\n"
              f'#include "prelude.h"\n\n')
    return header + "\n".join(bodies)


def main() -> None:
    for ref, label, out in [(FIX, "修正後", "case1_after.c"),
                            (PARENT, "修正前", "case1_before.c")]:
        (HERE / out).write_text(build(ref, label))
        print(f"wrote {out}")


if __name__ == "__main__":
    main()
