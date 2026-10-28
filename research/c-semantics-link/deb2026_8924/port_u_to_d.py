#!/usr/bin/env python3
"""U（上流）の証明 lean/Deb2026_8924U{1,0}.lean から、D（8.14.1）の証明 lean/Deb2026_8924D{1,0}.lean を機械的に作る。

1. 名前の置き換え（モジュール・名前空間）
2. 関数の形の違いの置き換え: 8.14.1 の is_public_suffix は int を返し、捨てるときは CERR_PSL（14）、
   そうでなければ CERR_OK（0）を返す（上流は bool の TRUE・FALSE）。仕様の戻り値の型・事後条件と、return の値を変える
"""
from pathlib import Path

LEAN = Path(__file__).resolve().parent.parent / "lean"
NAMES = [("GenDeb2026_8924U1", "GenDeb2026_8924D1"), ("GenDeb2026_8924U0", "GenDeb2026_8924D0"),
         ("Deb2026_8924U1", "Deb2026_8924D1"), ("Deb2026_8924U0", "Deb2026_8924D0"),
         ("Deb2026_8924_u1", "Deb2026_8924_d1"), ("Deb2026_8924_u0", "Deb2026_8924_d0"),
         ("Deb2026_8924U", "Deb2026_8924D")]
DOC = [  # 説明（コメント）だけ
    ("上流の修正後（U1、curl 51beed175d）の", "curl 8.14.1 に Debian の CVE-2026-8924.patch を当てたもの（D1）の"),
    ("上流の修正前（U0、curl 614b94eecc）の", "curl 8.14.1（D0、パッチを当てる前）の"),
    ("戻り値は `acc` が 0 なら真（Cookie を捨てる）、そうでなければ偽。",
     "戻り値は `acc` が 0 なら CERR_PSL（14、Cookie を捨てる）、そうでなければ CERR_OK（0）。"),
    ("/-- P1 の仕様: 戻り値は `acc` が 0 なら真。 -/", "/-- P1 の仕様: 戻り値は `acc` が 0 なら CERR_PSL（14）、そうでなければ CERR_OK（0）。 -/"),
    ("**P1（U1）**: 修正後の", "**P1（D1）**: パッチを当てた後の"),
    ("**P0（U0）**: 修正前の", "**P0（D0）**: パッチを当てる前の"),
    ("libpsl が受け入れると偽を返す（Cookie を捨てない）。", "libpsl が受け入れると CERR_OK を返す（Cookie を捨てない）。"),
    ("libpsl が受け入れる（`acc` が 0 でない）と、戻り値は偽（Cookie を捨てない）。",
     "libpsl が受け入れる（`acc` が 0 でない）と、戻り値は CERR_OK（Cookie を捨てない）。"),
]
SHAPE = [
    ("  tyres := tbool\n", "  tyres := tint\n"),
    ("post := fun v hp => v = Val.ofBool (Integers.Int.eq acc Integers.Int.zero) ∧ Hc c hp",
     "post := fun v hp => v = (if Integers.Int.eq acc Integers.Int.zero then .Vint (Integers.Int.repr 14)\n"
     "    else .Vint (Integers.Int.repr 0)) ∧ Hc c hp"),
    ("post := fun v hp => v = Val.ofBool false ∧ Hc c hp", "post := fun v hp => v = .Vint (Integers.Int.repr 0) ∧ Hc c hp"),
    ("(.Vint (Integers.Int.repr 0)) (Val.ofBool false) _", "(.Vint (Integers.Int.repr 0)) (.Vint (Integers.Int.repr 0)) _"),
    ("(.Vint (Integers.Int.repr 1)) (Val.ofBool true) _", "(.Vint (Integers.Int.repr 14)) (.Vint (Integers.Int.repr 14)) _"),
    # 事後条件が if になったので、acc の場合分けの仮定で if を簡約する
    ("⟨by rw [hφ], hH⟩", "⟨by simp [hφ], hH⟩"),
    ("exact ⟨by rw [ha], hH⟩", "exact ⟨by simp [ha], hH⟩"),
]


def port(text: str) -> str:
    for a, b in NAMES + DOC + SHAPE:
        text = text.replace(a, b)
    return text


def main() -> None:
    for side in ("1", "0"):
        src = LEAN / f"Deb2026_8924U{side}.lean"
        dst = LEAN / f"Deb2026_8924D{side}.lean"
        dst.write_text(port(src.read_text()))
        print(f"{src.name} -> {dst.name}")


if __name__ == "__main__":
    main()
