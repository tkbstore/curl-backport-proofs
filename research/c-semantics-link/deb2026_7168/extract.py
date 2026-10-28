#!/usr/bin/env python3
"""CVE-2026-7168（research/backport-proof-debian/cases/CVE-2026-7168.md）の4つの翻訳単位を作る。

- U1: curl c1cfdf59ac（上流の修正）の lib/setopt.c の setproxy と setopt_cptr_proxy
- U0: その親 7586ca7455 の setopt_cptr_proxy
- D0: curl 8.14.1 の lib/setopt.c の setopt_cptr（8.14.1 では CURLOPT_PROXY の処理がこの関数の switch の中にある）
- D1: 8.14.1 に Debian trixie の debian/patches/CVE-2026-7168.patch を `patch` でそのまま当てたものの setproxy と setopt_cptr。
      パッチのうち lib/ の部分（lib/setopt.c・lib/vauth/vauth.h）だけを当てる（tests/ は当てる先のファイルが無いため）。手では直さない
- enum dupstring はそれぞれの版の lib/urldata.h から、CURLoption の値はそれぞれの版の include/curl/curl.h から機械で作る

関数の本体は原文から機械で切り出す。前置き（prelude_u.h・prelude_d.h）と epilogue.h だけが手で用意した部分である。
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
U1 = "c1cfdf59acbaf9504c4578d4cf56cdd7c8594507"
U0 = "7586ca74558b7b0b21b2b8c83882172a6bc470eb"
OLD = "curl-8_14_1"
SRC = "lib/setopt.c"
VAUTH = "lib/vauth/vauth.h"
CURLH = "include/curl/curl.h"
HDR = "lib/urldata.h"
UFUNC = "setopt_cptr_proxy"
DFUNC = "setopt_cptr"
DEBIAN_COMMIT = "c2a97b9ea54e3ad6c4381c87a0ef235af2917863"  # salsa debian/curl の debian/trixie（8.14.1-2+deb13u6）
DEBIAN_PATCH = (f"https://salsa.debian.org/debian/curl/-/raw/{DEBIAN_COMMIT}"
                "/debian/patches/CVE-2026-7168.patch")
DEBIAN_PATCH_SHA256 = "0a61cb538b7651fc83ae2dd5b47d5002bdebd4b63257930e325c7a07444b142d"


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


def lib_part(patch_text: str) -> str:
    """パッチから lib/ のファイルの差分だけを取り出す（ヘッダの説明文は捨てる）。"""
    parts = re.split(r"(?m)^(?=diff --git )", patch_text)
    keep = [p for p in parts if re.match(r"diff --git a/lib/", p)]
    if not keep:
        sys.exit("no lib/ part in the Debian patch")
    return "".join(keep)


def apply_patch(files: dict[str, str], patch_text: str) -> dict[str, str]:
    """patch -p1 で当てる。当たらない hunk があれば止める（手では直さない）。"""
    with tempfile.TemporaryDirectory() as d:
        for name, text in files.items():
            target = Path(d) / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(text)
        res = subprocess.run(["patch", "-p1", "--no-backup-if-mismatch"], cwd=d,
                             input=patch_text, capture_output=True, text=True)
        if res.returncode != 0:
            sys.exit(f"Debian patch did not apply:\n{res.stdout}{res.stderr}")
        return {name: (Path(d) / name).read_text() for name in files}


def cut_function(src: str, name: str) -> str:
    """関数の定義（前方宣言ではないもの）を、行頭の `}` まで切り出す。"""
    for m in re.finditer(rf"^[A-Za-z_][^\n;]*\b{name}\(", src, re.MULTILINE):
        semi, brace = src.find(";", m.start()), src.find("{", m.start())
        if brace != -1 and (semi == -1 or brace < semi):
            end = src.find("\n}\n", m.start())
            if end < 0:
                sys.exit(f"end of function not found: {name}")
            return src[m.start():end + 2]
    sys.exit(f"function not found: {name}")


def cut_enum(src: str, name: str) -> str:
    m = re.search(rf"^enum {name} {{", src, re.MULTILINE)
    if m is None:
        sys.exit(f"enum not found: {name}")
    end = src.find("\n};\n", m.start())
    if end < 0:
        sys.exit(f"end of enum not found: {name}")
    return src[m.start():end + 4]


def unit(src: str, funcs: list[str], origin: str, define: str, prelude: str) -> str:
    header = (f"/* curl {SRC} @ {origin}\n"
              f" * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */\n"
              + (f"#define {define} 1\n" if define else "")
              + f'#include "{prelude}"\n\n')
    return (header + "\n".join(cut_function(src, f) for f in funcs)
            + f'\n#define DEB_KEEP {funcs[-1]}\n#include "epilogue.h"\n')


TYPES = {"CURLOPTTYPE_LONG": 0, "CURLOPTTYPE_OBJECTPOINT": 10000, "CURLOPTTYPE_FUNCTIONPOINT": 20000,
         "CURLOPTTYPE_OFF_T": 30000, "CURLOPTTYPE_BLOB": 40000, "CURLOPTTYPE_STRINGPOINT": 10000,
         "CURLOPTTYPE_SLISTPOINT": 10000, "CURLOPTTYPE_CBPOINT": 10000, "CURLOPTTYPE_VALUES": 0}


def curloption_enum(curlh: str) -> str:
    """include/curl/curl.h の CURLOPT(...)・CURLOPTDEPRECATED(...) の並びから CURLoption の値を作る。"""
    ents = re.findall(r"CURLOPT(?:DEPRECATED)?\(\s*(CURLOPT_\w+),\s*(CURLOPTTYPE_\w+),\s*(\d+)", curlh)
    if not ents:
        sys.exit("no CURLOPT entries")
    lines = [f"  {n} = {TYPES[t] + int(v)}," for n, t, v in ents]
    aliases = re.findall(r"^#define (CURLOPT_\w+)\s+(CURLOPT_\w+)\s*$", curlh, re.MULTILINE)
    alias_lines = "".join(f"#define {a} {b}\n" for a, b in aliases)
    return "typedef enum {\n" + "\n".join(lines) + "\n  CURLOPT_LASTENTRY\n} CURLoption;\n" + alias_lines


def main() -> None:
    u1, u0 = gh_raw(SRC, U1), gh_raw(SRC, U0)
    d0_src, d0_vauth = gh_raw(SRC, OLD), gh_raw(VAUTH, OLD)
    patch_text = fetch_debian_patch()
    d1 = apply_patch({SRC: d0_src, VAUTH: d0_vauth}, lib_part(patch_text))
    (HERE / "debian.patch").write_text(patch_text)
    (HERE / "deb2026_7168_u1.c").write_text(unit(u1, ["setproxy", UFUNC], f"{U1}（U1: 上流の修正後）", "DEB_U", "prelude_u.h"))
    (HERE / "deb2026_7168_u0.c").write_text(unit(u0, [UFUNC], f"{U0}（U0: 上流の修正前）", "DEB_U", "prelude_u.h"))
    (HERE / "deb2026_7168_d1.c").write_text(unit(d1[SRC], ["setproxy", DFUNC], f"{OLD} + Debian CVE-2026-7168.patch（D1）", "", "prelude_d.h"))
    (HERE / "deb2026_7168_d0.c").write_text(unit(d0_src, [DFUNC], f"{OLD}（D0）", "", "prelude_d.h"))
    if cut_enum(gh_raw(HDR, U1), "dupstring") != cut_enum(gh_raw(HDR, U0), "dupstring"):
        sys.exit("enum dupstring differs between U1 and U0")
    (HERE / "enum_u.h").write_text(cut_enum(gh_raw(HDR, U1), "dupstring"))
    (HERE / "enum_d.h").write_text(cut_enum(gh_raw(HDR, OLD), "dupstring"))
    if curloption_enum(gh_raw(CURLH, U1)) != curloption_enum(gh_raw(CURLH, U0)):
        sys.exit("CURLoption differs between U1 and U0")
    (HERE / "opt_u.h").write_text(curloption_enum(gh_raw(CURLH, U1)))
    (HERE / "opt_d.h").write_text(curloption_enum(gh_raw(CURLH, OLD)))
    print("wrote debian.patch deb2026_7168_{u1,u0,d1,d0}.c enum_{u,d}.h opt_{u,d}.h")


if __name__ == "__main__":
    main()
