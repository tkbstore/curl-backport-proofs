/-
CVE-2026-8927: 上流の修正（U1・U0）についての P1・P0（`research/backport-proof-debian/cases/CVE-2026-8927.md`）。

- `P1_C_U1`: 修正後の関数の仕様（`setproxies_after` が示したもの）の事後条件で、`Curl_safecmp` が偽（プロキシが変わった）
  なら `proxydigest.nonce` は NULL
- `P1_C_D1`・`P0_C_D0`: Debian の 8.14.1 の関数（`helper_after`・`helper_before`）について同じ形の定理
- `P0_C_U0`: 修正前の関数の仕様（`setproxies_before`）の事後条件では `proxydigest.nonce` は元のまま。
  場面 S の前提（ヒープと仮定）を満たす具体的な入力で、元の `nonce` は NULL でない
-/
import Deb2026_8927U1
import Deb2026_8927U0
import Deb2026_8927Witness
import Deb2026_8927D1
import Deb2026_8927D0
open CC CC.Sep CC.HProp

set_option maxRecDepth 20000

namespace Deb2026_8927

/-- **P1（U1）**: 修正後の関数が返した時点で、プロキシが変わっていれば（`same = false`）Digest の状態は消えている。 -/
theorem P1_C_U1 (c : Ctx) (q v : Val) (hp : Heap) (hpost : (U1.setSpecA c false q).post v hp) :
    v = .Vint (Integers.Int.repr 0) ∧ Cells c.pm (cellsU1 c (sFin1 c false q)) hp
    ∧ (sFin1 c false q).nonce = vnull :=
  ⟨hpost.1, hpost.2, rfl⟩

/-! ## P0（U0）の具体的な入力

1つのブロック（696 バイト）に置く。
  0: data（str[38]=304・str[39]=312 は NULL、str[50]=400 は 660 を指す、state.proxydigest.nonce=576 は 0 を指す）
  600: conn（origin 600→664、socks_proxy.peer 608=NULL、http_proxy.peer 624=NULL、proxytype 632=0、bits 640=0、scheme 648→672）
  660: no_proxy の先頭 'x'、664: origin->hostname（0 を指す）、672: scheme（protocol=1、flags=0）、688: proxy の先頭 'h'、689: peer の先頭 -/

def bw : Block := Mem.empty.nextblock
def ptr (o : Nat) : Val := .Vptr bw (Integers.Ptrofs.repr o)

def stores0 : Option Mem := do
  let m := (Mem.alloc Mem.empty 0 696).1
  let m ← Mem.store Mptr m bw 304 vnull
  let m ← Mem.store Mptr m bw 312 vnull
  let m ← Mem.store Mptr m bw 400 (ptr 660)
  let m ← Mem.store Mptr m bw 576 (ptr 0)
  let m ← Mem.store Mptr m bw 600 (ptr 664)
  let m ← Mem.store Mptr m bw 608 vnull
  let m ← Mem.store Mptr m bw 624 vnull
  let m ← Mem.store .Mint8unsigned m bw 632 (.Vint (Integers.Int.repr 0))
  let m ← Mem.store .Mint32 m bw 640 (.Vint (Integers.Int.repr 0))
  let m ← Mem.store Mptr m bw 648 (ptr 672)
  let m ← Mem.store .Mint8signed m bw 660 (.Vint (Integers.Int.repr 120))
  let m ← Mem.store Mptr m bw 664 (ptr 0)
  let m ← Mem.store .Mint64 m bw 672 (.Vlong (Integers.Int64.repr 1))
  let m ← Mem.store .Mint32 m bw 680 (.Vint (Integers.Int.repr 0))
  let m ← Mem.store .Mint8signed m bw 688 (.Vint (Integers.Int.repr 104))
  Mem.store .Mint8signed m bw 689 (.Vint (Integers.Int.repr 0))

theorem stores0_isSome : stores0.isSome = true := by decide

def mW0 : Mem := stores0.get stores0_isSome

def cW0 : Ctx where
  pm := .Freeable
  dataB := bw
  dataO := Integers.Ptrofs.repr 0
  connB := bw
  connO := Integers.Ptrofs.repr 600
  npB := bw
  npO := Integers.Ptrofs.repr 660
  np0 := Integers.Int.repr 120
  orgB := bw
  orgO := Integers.Ptrofs.repr 664
  hostB := bw
  hostO := Integers.Ptrofs.repr 0
  schB := bw
  schO := Integers.Ptrofs.repr 672
  proto := Integers.Int64.repr 1
  flags := Integers.Int.repr 0
  pB := bw
  pO := Integers.Ptrofs.repr 688
  pc := Integers.Int.repr 104
  peerB := bw
  peerO := Integers.Ptrofs.repr 689
  peer0 := Integers.Int.repr 0
  hpeer0 := vnull
  hpt0 := Integers.Int.repr 0
  envV := vnull
  nonce0 := ptr 0

/-- 場面 S の前提を満たすヒープが、具体的なメモリ `mW0` の上にある。 -/
theorem cells_cW0_satisfiable : ∃ hp, Cells cW0.pm (cellsU0 cW0 (s0 cW0)) hp ∧ Heap.Agrees hp mW0 :=
  cells_satisfiable mW0 _ (by decide) (by decide)

/-- **P0（U0）**: 前のプロキシの Digest の状態がある（`nonce` が NULL でない）入力で、場面 S の前提が満たせ、
    修正前の関数の事後条件では `nonce` は元のまま（プロキシが変わっても消えない）。 -/
theorem P0_C_U0 :
    ∃ c : Ctx, c.nonce0 ≠ vnull
      ∧ (∃ hp m, Cells c.pm (cellsU0 c (s0 c)) hp ∧ Heap.Agrees hp m)
      ∧ Integers.Int.eq (Integers.Int.sign_ext 8 c.pc) Integers.Int.zero = false
      ∧ Integers.Int.eq (Integers.Int.and c.flags
          (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 4))) Integers.Int.zero = true
      ∧ Integers.Int64.eq (Integers.Int64.and c.proto U0.famHttp) Integers.Int64.zero = false
      ∧ ∀ v hp, (U0.setSpecB c).post v hp →
          v = .Vint (Integers.Int.repr 0) ∧ Cells c.pm (cellsU0 c (sFin1 c true vnull)) hp
          ∧ (sFin1 c true vnull).nonce = c.nonce0 := by
  refine ⟨cW0, by decide, ?_, by decide, by decide, by decide, fun v hp h => ⟨h.1, h.2, rfl⟩⟩
  obtain ⟨hp, h1, h2⟩ := cells_cW0_satisfiable
  exact ⟨hp, mW0, h1, h2⟩

/-! ## Debian（D1・D0） -/

/-- **P1（D1）**: Debian のパッチを当てた 8.14.1 の関数が返した時点で、プロキシが変わっていれば Digest の状態は消えている。 -/
theorem P1_C_D1 (c : Ctx) (q v : Val) (hp : Heap) (hpost : (D1.helperSpecA c false q).post v hp) :
    v = .Vint (Integers.Int.repr 0) ∧ Cells c.pm (cellsD1 c (sFinD c false q)) hp
    ∧ (sFinD c false q).nonce = vnull :=
  ⟨hpost.1, hpost.2, rfl⟩

/-- D0 の具体的な入力（1つのブロック、752 バイト）。data は U0 と同じ位置。conn は 600 から:
  name 608→0、socks_proxy.host.rawalloc 616=NULL、http_proxy.host.rawalloc 656=NULL、proxytype 672=0、bits 696=0、
  handler 704→728、unix_domain_socket 712=NULL。720: no_proxy の先頭、728: handler（protocol=1、flags=0）、744: proxy の先頭、745: peer -/
def storesD : Option Mem := do
  let m := (Mem.alloc Mem.empty 0 752).1
  let m ← Mem.store Mptr m bw 304 vnull
  let m ← Mem.store Mptr m bw 312 vnull
  let m ← Mem.store Mptr m bw 400 (ptr 720)
  let m ← Mem.store Mptr m bw 576 (ptr 0)
  let m ← Mem.store Mptr m bw 608 (ptr 0)
  let m ← Mem.store Mptr m bw 616 vnull
  let m ← Mem.store Mptr m bw 656 vnull
  let m ← Mem.store .Mint8unsigned m bw 672 (.Vint (Integers.Int.repr 0))
  let m ← Mem.store .Mint32 m bw 696 (.Vint (Integers.Int.repr 0))
  let m ← Mem.store Mptr m bw 704 (ptr 728)
  let m ← Mem.store Mptr m bw 712 vnull
  let m ← Mem.store .Mint8signed m bw 720 (.Vint (Integers.Int.repr 120))
  let m ← Mem.store .Mint64 m bw 728 (.Vlong (Integers.Int64.repr 1))
  let m ← Mem.store .Mint32 m bw 736 (.Vint (Integers.Int.repr 0))
  let m ← Mem.store .Mint8signed m bw 744 (.Vint (Integers.Int.repr 104))
  Mem.store .Mint8signed m bw 745 (.Vint (Integers.Int.repr 0))

theorem storesD_isSome : storesD.isSome = true := by decide

def mWD : Mem := storesD.get storesD_isSome

def cWD0 : Ctx :=
  { cW0 with connO := Integers.Ptrofs.repr 600, npO := Integers.Ptrofs.repr 720,
             schO := Integers.Ptrofs.repr 728, pO := Integers.Ptrofs.repr 744,
             peerO := Integers.Ptrofs.repr 745 }

theorem cells_cWD0_satisfiable : ∃ hp, Cells cWD0.pm (cellsD0 cWD0 (s0 cWD0)) hp ∧ Heap.Agrees hp mWD :=
  cells_satisfiable mWD _ (by decide) (by decide)

/-- **P0（D0）**: 8.14.1（パッチ前）で、U0 と同じ形。 -/
theorem P0_C_D0 :
    ∃ c : Ctx, c.nonce0 ≠ vnull
      ∧ (∃ hp m, Cells c.pm (cellsD0 c (s0 c)) hp ∧ Heap.Agrees hp m)
      ∧ Integers.Int.eq (Integers.Int.sign_ext 8 c.pc) Integers.Int.zero = false
      ∧ Integers.Int.eq (Integers.Int.and c.flags
          (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 4))) Integers.Int.zero = true
      ∧ Integers.Int64.eq (Integers.Int64.and c.proto D0.famHttp) Integers.Int64.zero = false
      ∧ ∀ v hp, (D0.helperSpecB c).post v hp →
          v = .Vint (Integers.Int.repr 0) ∧ Cells c.pm (cellsD0 c (sFinD c true vnull)) hp
          ∧ (sFinD c true vnull).nonce = c.nonce0 := by
  refine ⟨cWD0, by decide, ?_, by decide, by decide, by decide, fun v hp h => ⟨h.1, h.2, rfl⟩⟩
  obtain ⟨hp, h1, h2⟩ := cells_cWD0_satisfiable
  exact ⟨hp, mWD, h1, h2⟩

end Deb2026_8927
