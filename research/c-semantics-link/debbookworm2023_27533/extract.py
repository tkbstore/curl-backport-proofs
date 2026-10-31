#!/usr/bin/env python3
"""CVE-2023-27533 bookworm（research/backport-proof-debian/cases/bookworm/CVE-2023-27533.md）の翻訳単位を作る。

入力は input/（auto/build.py の出力）。各版の lib/telnet.c の sha256 を input/manifest.json と照合してから使う。
4つの翻訳単位:
  debbookworm2023_27533_u1.c  上流の修正後 538b1e79a6（str_is_nonascii と check_telnet_options）
  debbookworm2023_27533_u0.c  上流の修正前 674a0662cf（check_telnet_options）
  debbookworm2023_27533_d1.c  curl-7_88_1 に Debian の CVE-2023-27533.patch を当てたもの（str_is_nonascii と check_telnet_options）
  debbookworm2023_27533_d0.c  curl-7_88_1（check_telnet_options）

関数の本体は原文から機械で切り出す。前置き（prelude.h）と epilogue.h だけが手で用意した部分である。
使い方: python3 extract.py
"""
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
INPUT = HERE / "input"
SRC = "lib/telnet.c"
SLOTS = {
    "u1": ("U1", ["str_is_nonascii", "check_telnet_options"], True, True),
    "u0": ("U0", ["check_telnet_options"], True, False),
    "d1": ("D1", ["str_is_nonascii", "check_telnet_options"], False, True),
    "d0": ("D0", ["check_telnet_options"], False, False),
}


def cut_function(src: str, name: str) -> str:
    """戻り値の型の行から始まり、行頭の `}` で終わる範囲を返す。前方宣言（`;` で終わる）は飛ばす。"""
    for m in re.finditer(rf"^(?:[A-Za-z_][^\n;]*\b)?{name}\(", src, re.MULTILINE):
        start = m.start()
        if src.startswith(name, start):
            start = src.rfind("\n", 0, start - 1) + 1
        body = src.find("\n{\n", m.start())
        if body < 0 or ";" in src[m.start():body]:
            continue
        end = src.find("\n}\n", body)
        if end < 0:
            sys.exit(f"end of function not found: {name}")
        return src[start:end + 2]
    sys.exit(f"function not found: {name}")


def main() -> None:
    manifest = json.loads((INPUT / "manifest.json").read_text())
    for key, (slot, funcs, up, after) in SLOTS.items():
        raw = (INPUT / slot / SRC).read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        if digest != manifest["files"][slot][SRC]:
            sys.exit(f"{slot}: sha256 mismatch {digest}")
        bodies = "\n".join(cut_function(raw.decode(), f) for f in funcs)
        header = (f"/* curl {SRC} ({slot}、input/{slot}/{SRC}、sha256 {digest})\n"
                  f" * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */\n"
                  + ("#define DEBBW_UP 1\n" if up else "")
                  + ("#define DEBBW_AFTER 1\n" if after else "")
                  + '#include "prelude.h"\n\n')
        (HERE / f"debbookworm2023_27533_{key}.c").write_text(header + bodies + '\n#include "epilogue.h"\n')
    print("wrote debbookworm2023_27533_{u1,u0,d1,d0}.c")


if __name__ == "__main__":
    main()
