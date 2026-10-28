#!/usr/bin/env python3
"""Case 3 のバックポート（research/backport-proof/PROTOCOL.md）の翻訳単位を作る。

1. curl 8.14.1 の lib/tftp.c を取得する（修正前）
2. 上流の修正 63dd390fab の lib/tftp.c の差分を `patch` で当てる
3. 当たらない hunk（tftp_send_first の2か所）は、同じ case ラベルに同じ行を入れて手で移す
4. バックポートの差分を backport.diff に残し、対象の関数の本体を切り出す

前置き（prelude.h）だけが手で用意した部分である。
使い方: python3 extract.py   （gh api で curl のソースを取得する。git の作業ツリーは使わない）
"""
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
OLD = "curl-8_14_1"
FIX = "63dd390fab905a239a97e2700532929343ebc4e9"
SRC = "lib/tftp.c"
FUNCS = ["tftp_send_first", "tftp_tx", "tftp_receive_packet"]  # 8.14.1 の tftp.c 内での出現順

# 手で移す hunk。上流の差分と同じ行を、8.14.1 の同じ case ラベルの直後に入れる
MANUAL = [
    ("  case TFTP_EVENT_ACK: /* Connected for transmit */\n"
     "    result = tftp_connect_for_tx(state, event);\n",
     "  case TFTP_EVENT_ACK: /* Connected for transmit */\n"
     "    if(!data->state.upload)\n"
     "      return CURLE_TFTP_ILLEGAL;\n"
     "    result = tftp_connect_for_tx(state, event);\n"),
    ("  case TFTP_EVENT_DATA: /* Connected for receive */\n"
     "    result = tftp_connect_for_rx(state, event);\n",
     "  case TFTP_EVENT_DATA: /* Connected for receive */\n"
     "    if(data->state.upload)\n"
     "      return CURLE_TFTP_ILLEGAL;\n"
     "    result = tftp_connect_for_rx(state, event);\n"),
]


def gh_raw(path: str, accept: str) -> str:
    out = subprocess.run(["gh", "api", "-H", f"Accept: {accept}", path],
                         check=True, capture_output=True, text=True)
    return out.stdout


def tftp_hunks(diff: str) -> str:
    """コミットの差分から lib/tftp.c の部分だけを取り出す。"""
    parts = re.split(r"(?m)^(?=diff --git )", diff)
    found = [p for p in parts if p.startswith(f"diff --git a/{SRC} ")]
    if len(found) != 1:
        sys.exit(f"{SRC} not found in the fix diff")
    return found[0]


def apply_patch(src: str, hunks: str) -> tuple[str, str]:
    """patch で当てる。戻り値は（当てた結果, patch の出力）。当たらない hunk があっても続ける。"""
    with tempfile.TemporaryDirectory() as d:
        target = Path(d) / "tftp.c"
        target.write_text(src)
        res = subprocess.run(["patch", "-p2", "--no-backup-if-mismatch", "-r", "-",
                              str(target)], input=hunks, capture_output=True, text=True)
        return target.read_text(), res.stdout + res.stderr


def apply_manual(src: str) -> str:
    for old, new in MANUAL:
        if src.count(old) != 1:
            sys.exit(f"manual hunk does not match exactly once:\n{old}")
        src = src.replace(old, new)
    return src


def cut_function(src: str, name: str) -> str:
    """関数の定義（前方宣言ではないもの）を、行頭の `}` まで切り出す。"""
    for m in re.finditer(rf"^[A-Za-z_][^\n;]*\b{name}\(", src, re.MULTILINE):
        semi, brace = src.find(";", m.start()), src.find("{", m.start())
        if brace != -1 and (semi == -1 or brace < semi):
            end = src.find("\n}\n", m.start())
            if end < 0:
                sys.exit(f"end of function not found: {name}")
            return src[m.start():end + 2]
    sys.exit(f"function definition not found: {name}")


def unit(src: str, label: str) -> str:
    bodies = [cut_function(src, f) for f in FUNCS]
    header = (f"/* curl {SRC} @ {OLD} ({label})\n"
              f" * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */\n"
              f'#include "prelude.h"\n\n')
    return header + "\n".join(bodies) + '\n#include "epilogue.h"\n'


def main() -> None:
    old = gh_raw(f"repos/curl/curl/contents/{SRC}?ref={OLD}",
                 "application/vnd.github.raw")
    hunks = tftp_hunks(gh_raw(f"repos/curl/curl/commits/{FIX}",
                              "application/vnd.github.diff"))
    patched, log = apply_patch(old, hunks)
    print(log.strip())
    backported = apply_manual(patched)
    with tempfile.TemporaryDirectory() as d:
        a, b = Path(d) / "a.c", Path(d) / "b.c"
        a.write_text(old)
        b.write_text(backported)
        diff = subprocess.run(["diff", "-u", "--label", f"a/{SRC} ({OLD})",
                               "--label", f"b/{SRC} (backport of {FIX[:10]})",
                               str(a), str(b)], capture_output=True, text=True).stdout
    (HERE / "backport.diff").write_text(diff)
    (HERE / "case3bp_before.c").write_text(unit(old, "バックポート前"))
    (HERE / "case3bp_after.c").write_text(unit(backported, "バックポート後"))
    print("wrote backport.diff case3bp_before.c case3bp_after.c")


if __name__ == "__main__":
    main()
