#!/usr/bin/env python3
"""Case 3 の翻訳単位を、curl のソースから関数の本体をそのまま切り出して作る。

前置き（prelude.h）だけが手で用意した部分である。
使い方: python3 extract.py   （gh api で curl のソースを取得する。git の作業ツリーは使わない）
"""
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FIX = "63dd390fab905a239a97e2700532929343ebc4e9"
PARENT = "3a397f7a05a46521b2772670b92ffda53fe05598"
SRC = "lib/tftp.c"
FUNCS = ["tftp_tx", "tftp_send_first", "tftp_receive_packet"]


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
    return header + "\n".join(bodies) + '\n#include "epilogue.h"\n'


def main() -> None:
    for ref, label, out in [(FIX, "修正後", "case3_after.c"),
                            (PARENT, "修正前", "case3_before.c")]:
        (HERE / out).write_text(build(ref, label))
        print(f"wrote {out}")


if __name__ == "__main__":
    main()
