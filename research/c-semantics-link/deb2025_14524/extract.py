#!/usr/bin/env python3
"""CVE-2025-14524（research/backport-proof-debian/cases/CVE-2025-14524.md）の4つの翻訳単位を作る。

U1: 上流の修正後（1a822275d3）、U0: その親（bb134bba29）
D1: curl 8.14.1 に Debian trixie の debian/patches/CVE-2025-14524.patch を当てたもの、D0: 当てる前の 8.14.1

上流は 8.14.1 のあとで Curl_sasl_start を sasl_choose_* に分けた。U では Curl_sasl_start と、
この構成で呼ばれる sasl_choose_* の本体と struct sasl_ctx を切り出す。D では Curl_sasl_start だけを切り出す

- Debian のパッチは lib/curl_sasl.c の部分だけを取り出して `patch` で当てる（このパッチは lib/curl_sasl.c だけを変える）。hunk は手で直さない
- 関数の本体と struct sasl_ctx は原文から切り出す。enum dupstring も各版の lib/urldata.h から切り出す（enum_u.h・enum_d.h）
- 前置き（prelude.h）だけが手で用意した部分である（Curl_sasl_start は static でなく、sasl_choose_* はそこから参照されるので消えない）
- 最後に clightgen -lean -normalize で ../lean/GenDeb2025_14524{U1,U0,D1,D0}.lean を作る

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
SRC = "lib/curl_sasl.c"
FUNCS_U = ["sasl_choose_external", "sasl_choose_oauth", "sasl_choose_oauth2", "sasl_choose_plain",
           "sasl_choose_login", "Curl_sasl_start"]
FUNCS_D = ["Curl_sasl_start"]
U1 = "1a822275d333dc6da6043497160fd04c8fa48640"
U0 = "bb134bba293ffd2128a43d17137e1fb2a84bdd47"
OLD = "curl-8_14_1"
DEBIAN_COMMIT = "c2a97b9ea54e3ad6c4381c87a0ef235af2917863"  # salsa debian/curl の debian/trixie（8.14.1-2+deb13u6）
DEBIAN_PATCH = (f"https://salsa.debian.org/debian/curl/-/raw/{DEBIAN_COMMIT}"
                "/debian/patches/CVE-2025-14524.patch")
DEBIAN_PATCH_SHA256 = "ca0c84dd96a3aa033d5b1401d46d1b64b3a8c86663d45573dd2a8e4f832683af"
NAME = "deb2025_14524"


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


def only_file(patch_text: str, path: str) -> str:
    """git 形式のパッチから、`path` を変える部分（diff --git から次の diff --git まで）だけを返す。"""
    parts = re.split(r"(?m)^(?=diff --git )", patch_text)
    keep = [p for p in parts if p.startswith(f"diff --git a/{path} b/{path}\n")]
    if len(keep) != 1:
        sys.exit(f"expected exactly one section for {path}, got {len(keep)}")
    return keep[0]


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
    """関数の定義を返す。戻り値の型が前の行にある書き方（`static CURLcode\\nname(`）にも対応する。"""
    m = re.search(rf"^(?:[A-Za-z_][^\n;]*\b)?{name}\(", src, re.MULTILINE)
    if m is None:
        sys.exit(f"function not found: {name}")
    start = m.start()
    if src.startswith(name, start):  # 型は前の行
        start = src.rfind("\n", 0, start - 1) + 1
    end = src.find("\n}\n", m.start())
    if end < 0:
        sys.exit(f"end of function not found: {name}")
    return src[start:end + 2]


def cut_enum(src: str, name: str) -> str:
    m = re.search(rf"^enum {name} {{", src, re.MULTILINE)
    if m is None:
        sys.exit(f"enum not found: {name}")
    end = src.find("\n};\n", m.start())
    if end < 0:
        sys.exit(f"end of enum not found: {name}")
    return src[m.start():end + 4]


def cut_struct(src: str, name: str) -> str:
    m = re.search(rf"^struct {name} {{", src, re.MULTILINE)
    if m is None:
        sys.exit(f"struct not found: {name}")
    end = src.find("\n};\n", m.start())
    if end < 0:
        sys.exit(f"end of struct not found: {name}")
    return src[m.start():end + 4]


def unit(src: str, ref: str, label: str, side: str) -> str:
    if side == "U":
        bodies = [cut_struct(src, "sasl_ctx")] + [cut_function(src, f) for f in FUNCS_U]
    else:
        bodies = [cut_function(src, f) for f in FUNCS_D]
    header = (f"/* curl {SRC} @ {ref} ({label})\n"
              f" * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */\n"
              f"#define SIDE_{side} 1\n"
              f'#include "enum_{side.lower()}.h"\n'
              f'#include "prelude.h"\n\n')
    return header + "\n".join(bodies) + "\n"


def main() -> None:
    u1, u0, d0 = gh_raw(SRC, U1), gh_raw(SRC, U0), gh_raw(SRC, OLD)
    patch_text = fetch_debian_patch()
    d1 = apply_patch(d0, only_file(patch_text, SRC))
    (HERE / "debian.patch").write_text(patch_text)
    (HERE / f"{NAME}_u1.c").write_text(unit(u1, U1, "上流の修正後", "U"))
    (HERE / f"{NAME}_u0.c").write_text(unit(u0, U0, "上流の修正前", "U"))
    (HERE / f"{NAME}_d1.c").write_text(unit(d1, OLD, "Debian の CVE-2025-14524.patch を当てた後", "D"))
    (HERE / f"{NAME}_d0.c").write_text(unit(d0, OLD, "8.14.1、パッチを当てる前", "D"))
    (HERE / "enum_u.h").write_text(cut_enum(gh_raw("lib/urldata.h", U1), "dupstring"))
    (HERE / "enum_d.h").write_text(cut_enum(gh_raw("lib/urldata.h", OLD), "dupstring"))
    clightgen = Path.home() / "Documents/GitHub/_vendor/certora-clean/clightgen"
    for s in ["u1", "u0", "d1", "d0"]:
        out = HERE.parent / "lean" / f"GenDeb2025_14524{s.upper()}.lean"
        subprocess.run([str(clightgen), "-lean", "-normalize", "-o", str(out), f"{NAME}_{s}.c"],
                       cwd=HERE, check=True)
    print(f"wrote debian.patch {NAME}_{{u1,u0,d1,d0}}.c enum_u.h enum_d.h")


if __name__ == "__main__":
    main()
