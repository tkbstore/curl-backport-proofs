/-
CVE-2026-3784: P1・P0（`research/backport-proof-debian/cases/CVE-2026-3784.md`）。

- `P1_C_U1`・`P1_C_D1`: 修正後の `proxy_info_matches`（`U1.matches_after`・`D1.matches_after`）が真を返したなら、
  `Curl_timestrcmp` は user・passwd の対のどちらにも 0 を返していた（資格情報が同じ）
- `P0_C_U0`・`P0_C_D0`: 修正前の関数（`U0.matches_before`・`D0.matches_before`）は、`Curl_timestrcmp` が user の対に 0 でない値を返す
  （資格情報が違う）入力でも真を返す。前提を満たすヒープを具体的なメモリで示す
-/
import Deb2026_3784U1
import Deb2026_3784U0
import Deb2026_3784D1
import Deb2026_3784D0
open CC CC.Sep CC.HProp
open Deb2026_8927 (Cells cells_satisfiable)
open Case4C (IsPtr)

set_option maxRecDepth 20000

namespace Deb2026_3784

theorem ofBool_true {b : Bool} (h : Val.ofBool b = Val.ofBool true) : b = true := by
  cases b
  · exact absurd h (by decide)
  · rfl

theorem P1_C_U1 (c : Ctx) (se : Integers.Int) (ts : List Val → Integers.Int) (v : Val) (hp : Heap)
    (hpost : (U1.spec c se ts).post v hp) (htrue : v = Val.ofBool true) :
    Integers.Int.eq (ts [Val.loadResult Mptr c.uD, Val.loadResult Mptr c.uN]) Integers.Int.zero = true
    ∧ Integers.Int.eq (ts [Val.loadResult Mptr c.pD, Val.loadResult Mptr c.pN]) Integers.Int.zero = true := by
  have h := ofBool_true (hpost.1.symm.trans htrue)
  revert h
  cases Integers.Int.eq (ts [Val.loadResult Mptr c.uD, Val.loadResult Mptr c.uN]) Integers.Int.zero <;>
    cases Integers.Int.eq (ts [Val.loadResult Mptr c.pD, Val.loadResult Mptr c.pN]) Integers.Int.zero <;> simp

theorem P1_C_D1 (c : Ctx) (se : Integers.Int) (ts : List Val → Integers.Int) (v : Val) (hp : Heap)
    (hpost : (D1.spec c se ts).post v hp) (htrue : v = Val.ofBool true) :
    Integers.Int.eq (ts [Val.loadResult Mptr c.uD, Val.loadResult Mptr c.uN]) Integers.Int.zero = true
    ∧ Integers.Int.eq (ts [Val.loadResult Mptr c.pD, Val.loadResult Mptr c.pN]) Integers.Int.zero = true := by
  have h := ofBool_true (hpost.1.symm.trans htrue)
  revert h
  cases Integers.Int.eq (ts [Val.loadResult Mptr c.uD, Val.loadResult Mptr c.uN]) Integers.Int.zero <;>
    cases Integers.Int.eq (ts [Val.loadResult Mptr c.pD, Val.loadResult Mptr c.pN]) Integers.Int.zero <;> simp

def bw : Block := Mem.empty.nextblock
def ptr (o : Nat) : Val := .Vptr bw (Integers.Ptrofs.repr o)

/-- 2つの `struct proxy_info` を1つのブロックに置く（data は 0、needle は 32）。種類 0・port 80・名前は同じ値。
    user は data が 0 を、needle が 32 を指す（違う資格情報）。passwd はどちらも NULL。 -/
def stores (pch : Chunk) (poff ptoff : Nat) : Option Mem := do
  let m := (Mem.alloc Mem.empty 0 64).1
  let m ← Mem.store Mptr m bw 0 (ptr 0)
  let m ← Mem.store pch m bw poff (.Vint (Integers.Int.repr 80))
  let m ← Mem.store .Mint8unsigned m bw ptoff (.Vint (Integers.Int.repr 0))
  let m ← Mem.store Mptr m bw 16 (ptr 0)
  let m ← Mem.store Mptr m bw 24 (.Vlong (Integers.Int64.repr 0))
  let m ← Mem.store Mptr m bw 32 (ptr 0)
  let m ← Mem.store pch m bw (32 + poff) (.Vint (Integers.Int.repr 80))
  let m ← Mem.store .Mint8unsigned m bw (32 + ptoff) (.Vint (Integers.Int.repr 0))
  let m ← Mem.store Mptr m bw 48 (ptr 32)
  Mem.store Mptr m bw 56 (.Vlong (Integers.Int64.repr 0))

def cW : Ctx := ⟨bw, Integers.Ptrofs.repr 0, bw, Integers.Ptrofs.repr 32, Integers.Int.repr 0, Integers.Int.repr 0,
  Integers.Int.repr 80, Integers.Int.repr 80, ptr 0, ptr 0, ptr 0, ptr 32,
  .Vlong (Integers.Int64.repr 0), .Vlong (Integers.Int64.repr 0)⟩

/-- `Curl_timestrcmp` の例: どの対にも 1（違う）を返す。 -/
def tsDiff : List Val → Integers.Int := fun _ => Integers.Int.repr 1

theorem storesU_isSome : (stores .Mint16unsigned 8 10).isSome = true := by decide
theorem storesD_isSome : (stores .Mint32 8 12).isSome = true := by decide

theorem P0_C_U0 :
    ∃ (c : Ctx) (se : Integers.Int) (ts : List Val → Integers.Int),
      Integers.Int.eq (ts [Val.loadResult Mptr c.uD, Val.loadResult Mptr c.uN]) Integers.Int.zero = false
      ∧ (∃ hp m, Cells .Freeable (cells U0.lay c) hp ∧ Heap.Agrees hp m)
      ∧ ∀ v hp, (U0.spec c se).post v hp → v = Val.ofBool true := by
  refine ⟨cW, Integers.Int.repr 1, tsDiff, by decide, ?_, fun v hp h => by rw [h.1]; rfl⟩
  obtain ⟨hp, h1, h2⟩ := cells_satisfiable ((stores .Mint16unsigned 8 10).get storesU_isSome)
    (cells U0.lay cW) (by decide) (by decide)
  exact ⟨hp, _, h1, h2⟩

theorem P0_C_D0 :
    ∃ (c : Ctx) (se : Integers.Int) (ts : List Val → Integers.Int),
      Integers.Int.eq (ts [Val.loadResult Mptr c.uD, Val.loadResult Mptr c.uN]) Integers.Int.zero = false
      ∧ (∃ hp m, Cells .Freeable (cells D0.lay c) hp ∧ Heap.Agrees hp m)
      ∧ ∀ v hp, (D0.spec c se).post v hp → v = Val.ofBool true := by
  refine ⟨cW, Integers.Int.repr 1, tsDiff, by decide, ?_, fun v hp h => by rw [h.1]; rfl⟩
  obtain ⟨hp, h1, h2⟩ := cells_satisfiable ((stores .Mint32 8 12).get storesD_isSome)
    (cells D0.lay cW) (by decide) (by decide)
  exact ⟨hp, _, h1, h2⟩

end Deb2026_3784
