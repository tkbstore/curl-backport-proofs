#!/usr/bin/env python3
"""U（上流）の証明 lean/Deb2026_3783U{1,0}.lean から、D（8.14.1）の証明 lean/Deb2026_3783D{1,0}.lean を機械的に作る。

1. 名前の置き換え（モジュール・名前空間）
2. 構造体の違いの置き換え: 8.14.1 の struct auth の want・picked・avail は unsigned long（上流は uint32_t）なので、
   picked の型（tuint → tulong）・セルの chunk（Mint32 → Mint64）・値（Vint 64 → Vlong 64）と、
   picked（4 → 8）・done/multipass の単位（12 → 24）のオフセットが変わる
"""
from pathlib import Path

LEAN = Path(__file__).resolve().parent.parent / "lean"
NAMES = [("GenDeb2026_3783U1", "GenDeb2026_3783D1"), ("GenDeb2026_3783U0", "GenDeb2026_3783D0"),
         ("Deb2026_3783U1", "Deb2026_3783D1"), ("Deb2026_3783U0", "Deb2026_3783D0"),
         ("Deb2026_3783_u1", "Deb2026_3783_d1"), ("Deb2026_3783_u0", "Deb2026_3783_d0"),
         ("Deb2026_3783U", "Deb2026_3783D")]
DOC = [  # 冒頭の説明（コメント）だけ
    ("上流の修正後（U1、curl e3d7401a32）の", "curl 8.14.1 に Debian の CVE-2026-3783.patch を当てたもの（D1）の"),
    ("上流の修正前（U0、curl 1495489c41）の", "curl 8.14.1（D0、パッチを当てる前）の"),
]
STRUCT = [
    ("(.Mint32, c.pm, c.aB, addr c.aO 4, .Vint (Integers.Int.repr 64))",
     "(.Mint64, c.pm, c.aB, addr c.aO 8, .Vlong (Integers.Int64.repr 64))"),
    ("(.Mint32, c.pm, c.aB, addr c.aO 12, .Vint w)", "(.Mint32, c.pm, c.aB, addr c.aO 24, .Vint w)"),
    ("= .OK (4, .Full) := by decide", "= .OK (8, .Full) := by decide"),
    ("= .OK (12, .Bits .I32 .Unsigned 0 1) := by decide", "= .OK (24, .Bits .I32 .Unsigned 0 1) := by decide"),
    ("= .OK (12, .Bits .I32 .Unsigned 1 1) := by decide", "= .OK (24, .Bits .I32 .Unsigned 1 1) := by decide"),
    ("_picked tuint)", "_picked tulong)"),
    ("(DerefLoc.value .Mint32 _ rfl (load_cell 0", "(DerefLoc.value .Mint64 _ rfl (load_cell 0"),
    ("(.Vint (Integers.Int.repr 64))", "(.Vlong (Integers.Int64.repr 64))"),
    ("(Integers.Ptrofs.add c.aO (Integers.Ptrofs.repr 12))", "(Integers.Ptrofs.add c.aO (Integers.Ptrofs.repr 24))"),
]


def port(text: str) -> str:
    for a, b in NAMES:
        text = text.replace(a, b)
    for a, b in DOC + STRUCT:
        text = text.replace(a, b)
    return text


def main() -> None:
    for s in ["1", "0"]:
        src = (LEAN / f"Deb2026_3783U{s}.lean").read_text()
        (LEAN / f"Deb2026_3783D{s}.lean").write_text(port(src))
    print("wrote Deb2026_3783D1.lean Deb2026_3783D0.lean")


if __name__ == "__main__":
    main()
