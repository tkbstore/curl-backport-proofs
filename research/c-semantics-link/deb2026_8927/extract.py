#!/usr/bin/env python3
"""CVE-2026-8927（research/backport-proof-debian/cases/CVE-2026-8927.md）の4つの翻訳単位を作る。

- U1: curl 5c225384b8（上流の修正）の lib/url.c の url_set_conn_proxies
- U0: その親 d99dcfb04a の同じ関数
- D0: curl 8.14.1 の lib/url.c の create_conn_helper_init_proxy
- D1: 8.14.1 に Debian trixie の debian/patches/CVE-2026-8927.patch を `patch` でそのまま当てたものの同じ関数。
      パッチのうち lib/ の部分（lib/url.c・lib/urldata.h）だけを当てる（tests/ は当てる先のファイルが無いため）。手では直さない
- enum dupstring は、それぞれの版の lib/urldata.h から切り出す（D1 は D0 と同じ。パッチは enum を変えない）

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
U1 = "5c225384b8d52c67ce8259c6e4203bc57aacb567"
U0 = "d99dcfb04a70fa0e49a7745de63ed6041e5b67f5"
OLD = "curl-8_14_1"
SRC = "lib/url.c"
HDR = "lib/urldata.h"
UFUNC = "url_set_conn_proxies"
DFUNC = "create_conn_helper_init_proxy"
DEBIAN_COMMIT = "c2a97b9ea54e3ad6c4381c87a0ef235af2917863"  # salsa debian/curl の debian/trixie（8.14.1-2+deb13u6）
DEBIAN_PATCH = (f"https://salsa.debian.org/debian/curl/-/raw/{DEBIAN_COMMIT}"
                "/debian/patches/CVE-2026-8927.patch")
DEBIAN_PATCH_SHA256 = "ba1ffbdacc8ad33571dcce8955145b4f3493eb9830a22d31e74993128140aa45"


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


def unit(src: str, func: str, origin: str, define: str, prelude: str) -> str:
    header = (f"/* curl {SRC} @ {origin}\n"
              f" * 関数の本体は extract.py が原文から切り出したもの。手で編集しない。 */\n"
              + (f"#define {define} 1\n" if define else "")
              + f'#include "{prelude}"\n\n')
    return header + cut_function(src, func) + f'\n#define DEB_KEEP {func}\n#include "epilogue.h"\n'


def main() -> None:
    u1, u0 = gh_raw(SRC, U1), gh_raw(SRC, U0)
    d0_src, d0_hdr = gh_raw(SRC, OLD), gh_raw(HDR, OLD)
    patch_text = fetch_debian_patch()
    lib_patch = lib_part(patch_text)
    d1 = apply_patch({SRC: d0_src, HDR: d0_hdr}, lib_patch)
    (HERE / "debian.patch").write_text(patch_text)
    (HERE / "deb2026_8927_u1.c").write_text(unit(u1, UFUNC, f"{U1}（U1: 上流の修正後）", "DEB_U1", "prelude_u.h"))
    (HERE / "deb2026_8927_u0.c").write_text(unit(u0, UFUNC, f"{U0}（U0: 上流の修正前）", "", "prelude_u.h"))
    (HERE / "deb2026_8927_d1.c").write_text(unit(d1[SRC], DFUNC, f"{OLD} + Debian CVE-2026-8927.patch（D1）", "DEB_D1", "prelude_d.h"))
    (HERE / "deb2026_8927_d0.c").write_text(unit(d0_src, DFUNC, f"{OLD}（D0）", "", "prelude_d.h"))
    (HERE / "enum_u1.h").write_text(cut_enum(gh_raw(HDR, U1), "dupstring"))
    (HERE / "enum_u0.h").write_text(cut_enum(gh_raw(HDR, U0), "dupstring"))
    if cut_enum(d1[HDR], "dupstring") != cut_enum(d0_hdr, "dupstring"):
        sys.exit("Debian patch changed enum dupstring")
    (HERE / "enum_d.h").write_text(cut_enum(d0_hdr, "dupstring"))
    print("wrote debian.patch deb2026_8927_{u1,u0,d1,d0}.c enum_{u1,u0,d}.h")


if __name__ == "__main__":
    main()
