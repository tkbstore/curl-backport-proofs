#!/usr/bin/env python3
"""CVE-2025-13034 trixie（research/backport-proof-debian/cases/trixie/CVE-2025-13034.md）の翻訳単位を作る。

入力は input/（auto/build.py の出力）。各版の lib/vquic/vquic-tls.c の sha256 を input/manifest.json と照合してから使う。
4つの翻訳単位:
  debtrixie2025_13034_u1.c  上流の修正後 3d91ca8cdb（前置き prelude_u.h。Case 4 の case4/prelude.h の写し）
  debtrixie2025_13034_u0.c  上流の修正前 dc34498d18（同上）
  debtrixie2025_13034_d1.c  curl-8_14_1 に Debian の series をこのパッチまで当てたもの（前置き prelude_d.h。case4deb/prelude.h の写し）
  debtrixie2025_13034_d0.c  curl-8_14_1 に series をこのパッチの直前まで当てたもの（同上）

関数の本体は原文から機械で切り出す。前置き（prelude_*.h・enum_*.h）だけが手で用意した部分である。
使い方: python3 extract.py
"""
import hashlib
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
INPUT = HERE / "input"
SRC = "lib/vquic/vquic-tls.c"
FUNC = "Curl_vquic_tls_verify_peer"
SLOTS = {"u1": ("U1", "prelude_u.h"), "u0": ("U0", "prelude_u.h"),
         "d1": ("D1", "prelude_d.h"), "d0": ("D0", "prelude_d.h")}


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


def main() -> None:
    manifest = json.loads((INPUT / "manifest.json").read_text())
    for key, (slot, prelude) in SLOTS.items():
        raw = (INPUT / slot / SRC).read_bytes()
        digest = hashlib.sha256(raw).hexdigest()
        if digest != manifest["files"][slot][SRC]:
            sys.exit(f"{slot}: sha256 mismatch {digest}")
        body = cut_function(raw.decode(), FUNC)
        given = (INPUT / "functions" / slot / f"{FUNC}.c").read_text()
        if body.rstrip("\n") != given.rstrip("\n"):
            sys.exit(f"{slot}: cut function differs from input/functions")
        header = (f"/* curl {SRC} ({slot}、input/{slot}/{SRC}、sha256 {digest})\n"
                  f" * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */\n"
                  f'#include "{prelude}"\n\n')
        (HERE / f"debtrixie2025_13034_{key}.c").write_text(header + body)
    print("wrote debtrixie2025_13034_{u1,u0,d1,d0}.c")


if __name__ == "__main__":
    main()
