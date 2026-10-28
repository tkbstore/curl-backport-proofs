#!/usr/bin/env python3
"""CVE-2026-8924（research/backport-proof-debian/cases/CVE-2026-8924.md）の4つの翻訳単位を作る。

U1: 上流の修正後（51beed175d）、U0: その親（614b94eecc）
D1: curl 8.14.1 に Debian trixie の debian/patches/CVE-2026-8924.patch を当てたもの、D0: 当てる前の 8.14.1

- Debian のパッチは lib/cookie.c の部分だけを取り出して `patch` で当てる（テストのファイルは除く）。hunk は手で直さない
- 関数の本体は原文から切り出す
- 前置き（prelude.h）と、static の関数を残すための後置き（epilogue.h）だけが手で用意した部分である
- 最後に clightgen -lean -normalize で ../lean/GenDeb2026_8924{U1,U0,D1,D0}.lean を作る

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
SRC = "lib/cookie.c"
FUNCS = ["is_public_suffix"]
U1 = "51beed175dbfc37da3113f6acce60c630c070ce8"
U0 = "614b94eeccc9e798a5592baaa784df763bd85528"
OLD = "curl-8_14_1"
DEBIAN_COMMIT = "c2a97b9ea54e3ad6c4381c87a0ef235af2917863"  # salsa debian/curl の debian/trixie（8.14.1-2+deb13u6）
DEBIAN_PATCH = (f"https://salsa.debian.org/debian/curl/-/raw/{DEBIAN_COMMIT}"
                "/debian/patches/CVE-2026-8924.patch")
DEBIAN_PATCH_SHA256 = "67550b143b7642c10b7db8141daa8868878d75a24ddba8cd9ae73766e3a845cf"
NAME = "deb2026_8924"


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


def unit(src: str, ref: str, label: str, side: str) -> str:
    bodies = [cut_function(src, f) for f in FUNCS]
    header = (f"/* curl {SRC} @ {ref} ({label})\n"
              f" * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */\n"
              f"#define SIDE_{side} 1\n"
              f'#include "prelude.h"\n\n')
    return header + "\n".join(bodies) + '\n#include "epilogue.h"\n'


def main() -> None:
    u1, u0, d0 = gh_raw(SRC, U1), gh_raw(SRC, U0), gh_raw(SRC, OLD)
    patch_text = fetch_debian_patch()
    d1 = apply_patch(d0, only_file(patch_text, SRC))
    (HERE / "debian.patch").write_text(patch_text)
    (HERE / f"{NAME}_u1.c").write_text(unit(u1, U1, "上流の修正後", "U"))
    (HERE / f"{NAME}_u0.c").write_text(unit(u0, U0, "上流の修正前", "U"))
    (HERE / f"{NAME}_d1.c").write_text(unit(d1, OLD, "Debian の CVE-2026-8924.patch を当てた後", "D"))
    (HERE / f"{NAME}_d0.c").write_text(unit(d0, OLD, "8.14.1、パッチを当てる前", "D"))
    clightgen = Path.home() / "Documents/GitHub/_vendor/certora-clean/clightgen"
    for s in ["u1", "u0", "d1", "d0"]:
        out = HERE.parent / "lean" / f"GenDeb2026_8924{s.upper()}.lean"
        subprocess.run([str(clightgen), "-lean", "-normalize", "-o", str(out), f"{NAME}_{s}.c"],
                       cwd=HERE, check=True)
    print(f"wrote debian.patch {NAME}_{{u1,u0,d1,d0}}.c")


if __name__ == "__main__":
    main()
