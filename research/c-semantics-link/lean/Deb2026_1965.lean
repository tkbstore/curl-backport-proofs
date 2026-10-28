/-
CVE-2026-1965（Debian の `_2`）: C の意味論の上での P1・P0（`research/backport-proof-debian/cases/CVE-2026-1965.md`）。

- P1（U1・D1）: `want_nego_http` が 1、`want_proxy_nego_http` が 0 なら、TRUE を返すのは `http_negotiate_state` が
  `GSS_AUTHNONE` でないときだけで、そのとき判定は `forceReuse`（`m->found = conn`、`m->force_reuse = TRUE`）
- P0（U0・D0）: 具体的なメモリ `mW` の上に前提を満たすヒープがあり、その入力（`want_nego_http` だけが 1、
  認証情報が一致、`http_negotiate_state` が `GSS_AUTHNONE`）で、判定は `accept`（TRUE を返し、何も書かない）
-/
import Deb2026_1965U1
import Deb2026_1965U0
import Deb2026_1965D1
import Deb2026_1965D0
import Case5Witness
open CC CC.Sep CC.HProp
open Case5C (addr bitOf cell mapsto_disj agrees_union)
open Case4C (IsPtr)

set_option maxRecDepth 20000

namespace Deb2026_1965C

/-- 判定の上での P1。`gateU1` の判定は、Negotiate を求めるとき、済んでいない接続を TRUE で受け入れない。 -/
theorem p1_verdict (c : Ctx) (w : Integers.Int) (cmp : Val → Val → Integers.Int)
    (hwn : bitOf w 2 = true) (hwpn : bitOf w 3 = false)
    (hret : retOf (vdOf gateU1 c w cmp) = true) :
    Integers.Int.eq c.hns Integers.Int.zero = false ∧ vdOf gateU1 c w cmp = .forceReuse := by
  unfold vdOf verdict gateU1 at *
  rw [hwn, hwpn] at *
  cases h1 : Integers.Int.eq (cmp c.nu c.cu) Integers.Int.zero <;>
  cases h2 : Integers.Int.eq (cmp c.np c.cp) Integers.Int.zero <;>
  cases h3 : Integers.Int.eq c.hns Integers.Int.zero <;>
  simp_all [retOf]

/-- **P1（U1）**: 上流の修正後の関数は `negoSpec gateU1` を満たし、その判定は上の性質を持つ。 -/
theorem P1_C (ge : CGenv) (c : Ctx) (fv : Val) (w : Integers.Int)
    (cmp : Val → Val → Integers.Int) (L : Layout ge.genv_cenv)
    (hpr : permOrder c.pm .Readable = true) (hpw : permOrder c.pm .Writable = true)
    (hptr : Ptrs c) (X : TsExt ge cmp) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_1965_u1.f_url_match_auth_nego)
      (negoSpec gateU1 c fv w cmp) vs)
    ∧ (bitOf w 2 = true → bitOf w 3 = false → retOf (vdOf gateU1 c w cmp) = true →
        Integers.Int.eq c.hns Integers.Int.zero = false ∧ vdOf gateU1 c w cmp = .forceReuse) :=
  ⟨nego_u1 ge c fv w cmp L hpr hpw hptr X, p1_verdict c w cmp⟩

/-- **P1（D1）**: 8.14.1 に Debian の `_1`・`_2` を当てた関数で、`P1_C` と同じ形。 -/
theorem P1_D (ge : CGenv) (c : Ctx) (fv : Val) (w : Integers.Int)
    (cmp : Val → Val → Integers.Int) (L : Layout ge.genv_cenv)
    (hpr : permOrder c.pm .Readable = true) (hpw : permOrder c.pm .Writable = true)
    (hptr : Ptrs c) (X : TsExt ge cmp) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_1965_d1.f_url_match_auth_nego)
      (negoSpec gateU1 c fv w cmp) vs)
    ∧ (bitOf w 2 = true → bitOf w 3 = false → retOf (vdOf gateU1 c w cmp) = true →
        Integers.Int.eq c.hns Integers.Int.zero = false ∧ vdOf gateU1 c w cmp = .forceReuse) :=
  ⟨nego_d1 ge c fv w cmp L hpr hpw hptr X, p1_verdict c w cmp⟩

/-! ## 前提を満たす具体的なメモリ（1つのブロック、64 バイト）

  オフセット  中身
   0  m->found = NULL
   8  m->needle = ブロックの 24
  16  m のビットの単位 = 4（want_nego_http だけが 1）
  24  needle->user = NULL、32 needle->passwd = NULL
  40  conn->user = NULL、48 conn->passwd = NULL
  56  conn->http_negotiate_state = 0（GSS_AUTHNONE）、60 conn->proxy_negotiate_state = 0
-/

def bw : Block := Mem.empty.nextblock
def m0 : Mem := (Mem.alloc Mem.empty 0 64).1
def ptr (o : Nat) : Val := .Vptr bw (Integers.Ptrofs.repr o)

def storesW : Option Mem := do
  let m ← Mem.store Mptr m0 bw 0 (.Vlong (Integers.Int64.repr 0))
  let m ← Mem.store .Mint32 m bw 16 (.Vint (Integers.Int.repr 4))
  let m ← Mem.store Mptr m bw 8 (ptr 24)
  let m ← Mem.store Mptr m bw 24 (.Vlong (Integers.Int64.repr 0))
  let m ← Mem.store Mptr m bw 32 (.Vlong (Integers.Int64.repr 0))
  let m ← Mem.store Mptr m bw 40 (.Vlong (Integers.Int64.repr 0))
  let m ← Mem.store Mptr m bw 48 (.Vlong (Integers.Int64.repr 0))
  let m ← Mem.store .Mint32 m bw 56 (.Vint (Integers.Int.repr 0))
  Mem.store .Mint32 m bw 60 (.Vint (Integers.Int.repr 0))

theorem storesW_isSome : storesW.isSome = true := by decide

def mW : Mem := storesW.get storesW_isSome

def cW : Ctx where
  connB := bw
  connO := Integers.Ptrofs.repr 40
  mB := bw
  mO := Integers.Ptrofs.repr 0
  ndlB := bw
  ndlO := Integers.Ptrofs.repr 24
  nu := .Vlong (Integers.Int64.repr 0)
  np := .Vlong (Integers.Int64.repr 0)
  cu := .Vlong (Integers.Int64.repr 0)
  cp := .Vlong (Integers.Int64.repr 0)
  hns := Integers.Int.repr 0
  pns := Integers.Int.repr 0
  pm := .Freeable

def wW : Integers.Int := Integers.Int.repr 4
def fvW : Val := .Vlong (Integers.Int64.repr 0)
/-- 認証情報は一致する（`Curl_timestrcmp` は 0 を返す）。 -/
def cmpW : Val → Val → Integers.Int := fun _ _ => Integers.Int.repr 0

theorem cW_ptrs : Ptrs cW := ⟨Or.inr ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩⟩

theorem cW_cells : addr cW.mO 0 = 0 ∧ addr cW.mO 16 = 16 ∧ addr cW.mO 8 = 8 ∧ addr cW.ndlO 0 = 24 ∧ addr cW.ndlO 8 = 32 ∧ addr cW.connO 0 = 40 ∧ addr cW.connO 8 = 48 ∧ addr cW.connO 16 = 56 ∧ addr cW.connO 20 = 60 := by decide

theorem H_cW_satisfiable : ∃ hp, H cW fvW wW hp ∧ Heap.Agrees hp mW := by
  obtain ⟨a0, a16, a8, a24, a32, a40, a48, a56, a60⟩ := cW_cells
  obtain ⟨h1, m1, g1⟩ := cell (chunk := Mptr) (b := bw) (ofs := 0)
    (v := .Vlong (Integers.Int64.repr 0)) (m := mW) (by decide) (by decide)
  obtain ⟨h2, m2, g2⟩ := cell (chunk := .Mint32) (b := bw) (ofs := 16)
    (v := .Vint (Integers.Int.repr 4)) (m := mW) (by decide) (by decide)
  obtain ⟨h3, m3, g3⟩ := cell (chunk := Mptr) (b := bw) (ofs := 8)
    (v := ptr 24) (m := mW) (by decide) (by decide)
  obtain ⟨h4, m4, g4⟩ := cell (chunk := Mptr) (b := bw) (ofs := 24)
    (v := .Vlong (Integers.Int64.repr 0)) (m := mW) (by decide) (by decide)
  obtain ⟨h5, m5, g5⟩ := cell (chunk := Mptr) (b := bw) (ofs := 32)
    (v := .Vlong (Integers.Int64.repr 0)) (m := mW) (by decide) (by decide)
  obtain ⟨h6, m6, g6⟩ := cell (chunk := Mptr) (b := bw) (ofs := 40)
    (v := .Vlong (Integers.Int64.repr 0)) (m := mW) (by decide) (by decide)
  obtain ⟨h7, m7, g7⟩ := cell (chunk := Mptr) (b := bw) (ofs := 48)
    (v := .Vlong (Integers.Int64.repr 0)) (m := mW) (by decide) (by decide)
  obtain ⟨h8, m8, g8⟩ := cell (chunk := .Mint32) (b := bw) (ofs := 56)
    (v := .Vint (Integers.Int.repr 0)) (m := mW) (by decide) (by decide)
  obtain ⟨h9, m9, g9⟩ := cell (chunk := .Mint32) (b := bw) (ofs := 60)
    (v := .Vint (Integers.Int.repr 0)) (m := mW) (by decide) (by decide)
  have d1 : Heap.disjoint h1 (Heap.union h2 (Heap.union h3 (Heap.union h4 (Heap.union h5 (Heap.union h6 (Heap.union h7 (Heap.union h8 h9))))))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m2 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m3 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m4 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m5 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m6 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m7 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m8 (by decide), mapsto_disj m1 m9 (by decide)⟩⟩⟩⟩⟩⟩⟩
  have d2 : Heap.disjoint h2 (Heap.union h3 (Heap.union h4 (Heap.union h5 (Heap.union h6 (Heap.union h7 (Heap.union h8 h9)))))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m3 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m4 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m5 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m6 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m7 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m8 (by decide), mapsto_disj m2 m9 (by decide)⟩⟩⟩⟩⟩⟩
  have d3 : Heap.disjoint h3 (Heap.union h4 (Heap.union h5 (Heap.union h6 (Heap.union h7 (Heap.union h8 h9))))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m4 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m5 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m6 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m7 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m8 (by decide), mapsto_disj m3 m9 (by decide)⟩⟩⟩⟩⟩
  have d4 : Heap.disjoint h4 (Heap.union h5 (Heap.union h6 (Heap.union h7 (Heap.union h8 h9)))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m5 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m6 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m7 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m8 (by decide), mapsto_disj m4 m9 (by decide)⟩⟩⟩⟩
  have d5 : Heap.disjoint h5 (Heap.union h6 (Heap.union h7 (Heap.union h8 h9))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m5 m6 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m5 m7 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m5 m8 (by decide), mapsto_disj m5 m9 (by decide)⟩⟩⟩
  have d6 : Heap.disjoint h6 (Heap.union h7 (Heap.union h8 h9)) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m6 m7 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m6 m8 (by decide), mapsto_disj m6 m9 (by decide)⟩⟩
  have d7 : Heap.disjoint h7 (Heap.union h8 h9) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m7 m8 (by decide), mapsto_disj m7 m9 (by decide)⟩
  have d8 : Heap.disjoint h8 h9 :=
    mapsto_disj m8 m9 (by decide)
  refine ⟨_, ?_, agrees_union g1 (agrees_union g2 (agrees_union g3 (agrees_union g4 (agrees_union g5 (agrees_union g6 (agrees_union g7 (agrees_union g8 g9)))))))⟩
  unfold H
  rw [a0, a16, a8, a24, a32, a40, a48, a56, a60]
  exact ⟨_, _, d1, rfl, m1, _, _, d2, rfl, m2, _, _, d3, rfl, m3, _, _, d4, rfl, m4, _, _, d5, rfl, m5, _, _, d6, rfl, m6, _, _, d7, rfl, m7, _, _, d8, rfl, m8, m9⟩

theorem verdict_W :
    bitOf wW 2 = true ∧ bitOf wW 3 = false ∧ bitOf wW 0 = false ∧ bitOf wW 1 = false
    ∧ Integers.Int.eq cW.hns Integers.Int.zero = true
    ∧ vdOf gateU0 cW wW cmpW = .accept := by decide

/-- **P0（U0）**: 上流の修正前の関数は `negoSpec gateU0` を満たし、具体的なメモリ `mW` の上の入力で、
    Negotiate を求める要求が、Negotiate を済ませていない接続を TRUE（`accept`）で受け入れる。 -/
theorem P0_C (ge : CGenv) (L : Layout ge.genv_cenv) (X : TsExt ge cmpW) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_1965_u0.f_url_match_auth_nego)
      (negoSpec gateU0 cW fvW wW cmpW) vs)
    ∧ (∃ hp, H cW fvW wW hp ∧ Heap.Agrees hp mW)
    ∧ bitOf wW 2 = true ∧ bitOf wW 3 = false
    ∧ Integers.Int.eq cW.hns Integers.Int.zero = true
    ∧ vdOf gateU0 cW wW cmpW = .accept :=
  ⟨nego_u0 ge cW fvW wW cmpW L rfl rfl cW_ptrs X, H_cW_satisfiable,
   verdict_W.1, verdict_W.2.1, verdict_W.2.2.2.2.1, verdict_W.2.2.2.2.2⟩

/-- **P0（D0）**: 8.14.1 に Debian の `_1` だけを当てた関数で、`P0_C` と同じ形。 -/
theorem P0_D (ge : CGenv) (L : Layout ge.genv_cenv) (X : TsExt ge cmpW) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_1965_d0.f_url_match_auth_nego)
      (negoSpec gateU0 cW fvW wW cmpW) vs)
    ∧ (∃ hp, H cW fvW wW hp ∧ Heap.Agrees hp mW)
    ∧ bitOf wW 2 = true ∧ bitOf wW 3 = false
    ∧ Integers.Int.eq cW.hns Integers.Int.zero = true
    ∧ vdOf gateU0 cW wW cmpW = .accept :=
  ⟨nego_d0 ge cW fvW wW cmpW L rfl rfl cW_ptrs X, H_cW_satisfiable,
   verdict_W.1, verdict_W.2.1, verdict_W.2.2.2.2.1, verdict_W.2.2.2.2.2⟩

/-- 前提 `Layout` は、4つの翻訳単位それぞれの composite 環境で成り立つ。 -/
example : Layout Deb2026_1965_d1.prog.prog_comp_env ∧ Layout Deb2026_1965_d0.prog.prog_comp_env :=
  ⟨layout_d1, layout_d0⟩

end Deb2026_1965C
