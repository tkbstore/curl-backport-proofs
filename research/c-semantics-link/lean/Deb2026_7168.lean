/-
CVE-2026-7168: P1・P0（`research/backport-proof-debian/cases/CVE-2026-7168.md`）。

- `P1_C_U1`・`P1_C_D1`: 修正後の関数（`U1.cptr_proxy_after`・`D1.cptr_after`。`setproxy` は `U1.setproxy_ok`・`D1.setproxy_ok`）
  の事後条件で、プロキシが変わった（`same = false`）なら `proxydigest.nonce` は NULL、`authproxy.picked` は 0
- `P0_C_U0`・`P0_C_D0`: 修正前の関数（`U0.cptr_proxy_before`・`D0.cptr_before`）の事後条件では両方とも元のまま。
  前提を満たす具体的な入力で、元の値は NULL・0 でない
-/
import Deb2026_7168U1
import Deb2026_7168U0
import Deb2026_7168D1
import Deb2026_7168D0
open CC CC.Sep CC.HProp
open Deb2026_8927 (Cells cells_satisfiable vnull)

set_option maxRecDepth 20000

namespace Deb2026_7168

theorem P1_C_U1 (c : Ctx) (rs : Integers.Int) (sv v : Val) (hp : Heap)
    (hpost : (U1.cptrSpec c false rs sv).post v hp) :
    v = .Vint rs ∧ Cells .Freeable (cells layU c (sAfter layU c false sv)) hp
    ∧ (sAfter layU c false sv).nonce = vnull ∧ (sAfter layU c false sv).picked = layU.pzero :=
  ⟨hpost.1, hpost.2, rfl, rfl⟩

theorem P1_C_D1 (c : Ctx) (rs : Integers.Int) (sv v : Val) (hp : Heap)
    (hpost : (D1.cptrSpec c false rs sv).post v hp) :
    v = .Vint rs ∧ Cells .Freeable (cells layD c (sAfter layD c false sv)) hp
    ∧ (sAfter layD c false sv).nonce = vnull ∧ (sAfter layD c false sv).picked = layD.pzero :=
  ⟨hpost.1, hpost.2, rfl, rfl⟩

def bw : Block := Mem.empty.nextblock
def ptr (o : Nat) : Val := .Vptr bw (Integers.Ptrofs.repr o)

/-- U0 の入力: data は 0 から（str[32] = 264 → 472、proxydigest.nonce = 456 → 0、authproxy.picked = 464 は 1）、
    元のプロキシ文字列の先頭 472、新しい文字列の先頭 473。480 バイト。 -/
def storesU : Option Mem := do
  let m := (Mem.alloc Mem.empty 0 480).1
  let m ← Mem.store Mptr m bw 264 (ptr 472)
  let m ← Mem.store Mptr m bw 456 (ptr 0)
  let m ← Mem.store .Mint32 m bw 464 (.Vint (Integers.Int.repr 1))
  let m ← Mem.store .Mint8signed m bw 472 (.Vint (Integers.Int.repr 97))
  Mem.store .Mint8signed m bw 473 (.Vint (Integers.Int.repr 98))

theorem storesU_isSome : storesU.isSome = true := by decide
def mU : Mem := storesU.get storesU_isSome

def cU : Ctx := ⟨bw, Integers.Ptrofs.repr 0, bw, Integers.Ptrofs.repr 472, Integers.Int.repr 97,
  bw, Integers.Ptrofs.repr 473, Integers.Int.repr 98, ptr 0, .Vint (Integers.Int.repr 1)⟩

/-- D0 の入力: str[32] = 384 → 640、nonce = 616 → 0、picked = 624 は 1（unsigned long）、文字列の先頭 640・641。648 バイト。 -/
def storesD : Option Mem := do
  let m := (Mem.alloc Mem.empty 0 648).1
  let m ← Mem.store Mptr m bw 384 (ptr 640)
  let m ← Mem.store Mptr m bw 616 (ptr 0)
  let m ← Mem.store .Mint64 m bw 624 (.Vlong (Integers.Int64.repr 1))
  let m ← Mem.store .Mint8signed m bw 640 (.Vint (Integers.Int.repr 97))
  Mem.store .Mint8signed m bw 641 (.Vint (Integers.Int.repr 98))

theorem storesD_isSome : storesD.isSome = true := by decide
def mD : Mem := storesD.get storesD_isSome

def cD : Ctx := ⟨bw, Integers.Ptrofs.repr 0, bw, Integers.Ptrofs.repr 640, Integers.Int.repr 97,
  bw, Integers.Ptrofs.repr 641, Integers.Int.repr 98, ptr 0, .Vlong (Integers.Int64.repr 1)⟩

theorem P0_C_U0 :
    ∃ c : Ctx, c.nonce0 ≠ vnull ∧ c.picked0 ≠ layU.pzero
      ∧ (∃ hp m, Cells .Freeable (cells layU c (s0 c)) hp ∧ Heap.Agrees hp m)
      ∧ ∀ rs sv v hp, (U0.cptrSpecB c rs sv).post v hp →
          v = .Vint rs ∧ Cells .Freeable (cells layU c (sBefore c sv)) hp
          ∧ (sBefore c sv).nonce = c.nonce0 ∧ (sBefore c sv).picked = c.picked0 := by
  refine ⟨cU, by decide, by decide, ?_, fun rs sv v hp h => ⟨h.1, h.2, rfl, rfl⟩⟩
  obtain ⟨hp, h1, h2⟩ := cells_satisfiable mU (cells layU cU (s0 cU)) (by decide) (by decide)
  exact ⟨hp, mU, h1, h2⟩

theorem P0_C_D0 :
    ∃ c : Ctx, c.nonce0 ≠ vnull ∧ c.picked0 ≠ layD.pzero
      ∧ (∃ hp m, Cells .Freeable (cells layD c (s0 c)) hp ∧ Heap.Agrees hp m)
      ∧ ∀ rs sv v hp, (D0.cptrSpecB c rs sv).post v hp →
          v = .Vint rs ∧ Cells .Freeable (cells layD c (sBefore c sv)) hp
          ∧ (sBefore c sv).nonce = c.nonce0 ∧ (sBefore c sv).picked = c.picked0 := by
  refine ⟨cD, by decide, by decide, ?_, fun rs sv v hp h => ⟨h.1, h.2, rfl, rfl⟩⟩
  obtain ⟨hp, h1, h2⟩ := cells_satisfiable mD (cells layD cD (s0 cD)) (by decide) (by decide)
  exact ⟨hp, mD, h1, h2⟩

end Deb2026_7168
