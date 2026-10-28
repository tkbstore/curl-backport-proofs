/-
CVE-2026-5545: C の意味論の上での P1・P0（`research/backport-proof-debian/cases/CVE-2026-5545.md`）。

- P1（U1・D1）: `want_ntlm_http` が 1、認証情報が違い、`http_negotiate_state` が `GSS_AUTHNONE` でないなら、
  判定は `reject`（FALSE を返し、`m->found` も `force_reuse` も書かない）
- P0（U0・D0）: 具体的なメモリ `mW` の上に前提を満たすヒープがあり、その入力（`want_ntlm_http` が 1、認証情報が違う、
  `http_ntlm_state` が NONE、`http_negotiate_state` が NONE でない）で、判定は `candidate`（`m->found = conn`）
-/
import Deb2026_5545U1
import Deb2026_5545U0
import Deb2026_5545D1
import Deb2026_5545D0
import Case5Witness
open CC CC.Sep CC.HProp
open Case5C (addr bitOf cell mapsto_disj agrees_union)
open Case4C (IsPtr)

set_option maxRecDepth 20000

namespace Deb2026_5545C

/-- 判定の上での P1（修正後 `fix = true`）。 -/
theorem p1_verdict (c : Ctx) (w : Integers.Int) (cmp : Val → Val → Integers.Int) :
    bitOf w 0 = true →
    ((!Integers.Int.eq (cmp c.nu c.cu) Integers.Int.zero)
      || (!Integers.Int.eq (cmp c.np c.cp) Integers.Int.zero)) = true →
    Integers.Int.eq c.hns Integers.Int.zero = false → vdOf true c w cmp = .reject := by
  intro h1 h2 h3
  unfold vdOf verdict
  rw [h1, h2, h3]
  cases Integers.Int.eq c.hnt Integers.Int.zero <;> rfl

/-- **P1（U1）: 上流の修正後の関数は `ntlmSpec true` を満たし、Negotiate 済みで認証情報の違う接続を候補にしない。** -/
theorem P1_C (ge : CGenv) (c : Ctx) (fv : Val) (w : Integers.Int)
    (cmp : Val → Val → Integers.Int) (L : Layout ge.genv_cenv)
    (hpr : permOrder c.pm .Readable = true) (hpw : permOrder c.pm .Writable = true)
    (hptr : Ptrs c) (X : Deb2026_1965C.TsExt ge cmp) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_5545_u1.f_url_match_auth_ntlm)
      (ntlmSpec true c fv w cmp) vs)
    ∧ (bitOf w 0 = true →
        ((!Integers.Int.eq (cmp c.nu c.cu) Integers.Int.zero)
          || (!Integers.Int.eq (cmp c.np c.cp) Integers.Int.zero)) = true →
        Integers.Int.eq c.hns Integers.Int.zero = false → vdOf true c w cmp = .reject) :=
  ⟨ntlm_u1 ge c fv w cmp L hpr hpw hptr X, p1_verdict c w cmp⟩

/-- **P1（D1）: 8.14.1 に Debian のパッチを当てた関数で、`P1_C` と同じ形。** -/
theorem P1_D (ge : CGenv) (c : Ctx) (fv : Val) (w : Integers.Int)
    (cmp : Val → Val → Integers.Int) (L : Layout ge.genv_cenv)
    (hpr : permOrder c.pm .Readable = true) (hpw : permOrder c.pm .Writable = true)
    (hptr : Ptrs c) (X : Deb2026_1965C.TsExt ge cmp) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_5545_d1.f_url_match_auth_ntlm)
      (ntlmSpec true c fv w cmp) vs)
    ∧ (bitOf w 0 = true →
        ((!Integers.Int.eq (cmp c.nu c.cu) Integers.Int.zero)
          || (!Integers.Int.eq (cmp c.np c.cp) Integers.Int.zero)) = true →
        Integers.Int.eq c.hns Integers.Int.zero = false → vdOf true c w cmp = .reject) :=
  ⟨ntlm_d1 ge c fv w cmp L hpr hpw hptr X, p1_verdict c w cmp⟩

/-! ## 前提を満たす具体的なメモリ（1つのブロック、72 バイト）

  オフセット  中身
   0  m->found = NULL、8  m->needle = 24、16  m の単位 = 1（want_ntlm_http だけが 1）
  24・32  needle->user・passwd = NULL
  40・48  conn->user・passwd = NULL、56  http_ntlm_state = 0、60  proxy_ntlm_state = 0、64  http_negotiate_state = 1
  `Curl_timestrcmp` は 1 を返す（認証情報が違う。値は C の文字列ではなく、外部関数の仕様の上で与える）
-/

def bw : Block := Mem.empty.nextblock
def m0 : Mem := (Mem.alloc Mem.empty 0 72).1
def ptr (o : Nat) : Val := .Vptr bw (Integers.Ptrofs.repr o)

def storesW : Option Mem := do
  let m ← Mem.store Mptr m0 bw 0 (.Vlong (Integers.Int64.repr 0))
  let m ← Mem.store .Mint32 m bw 16 (.Vint (Integers.Int.repr 1))
  let m ← Mem.store Mptr m bw 8 (ptr 24)
  let m ← Mem.store Mptr m bw 24 (.Vlong (Integers.Int64.repr 0))
  let m ← Mem.store Mptr m bw 32 (.Vlong (Integers.Int64.repr 0))
  let m ← Mem.store Mptr m bw 40 (.Vlong (Integers.Int64.repr 0))
  let m ← Mem.store Mptr m bw 48 (.Vlong (Integers.Int64.repr 0))
  let m ← Mem.store .Mint32 m bw 56 (.Vint (Integers.Int.repr 0))
  let m ← Mem.store .Mint32 m bw 60 (.Vint (Integers.Int.repr 0))
  Mem.store .Mint32 m bw 64 (.Vint (Integers.Int.repr 1))

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
  hnt := Integers.Int.repr 0
  pnt := Integers.Int.repr 0
  hns := Integers.Int.repr 1
  pm := .Freeable

def wW : Integers.Int := Integers.Int.repr 1
def fvW : Val := .Vlong (Integers.Int64.repr 0)
def cmpW : Val → Val → Integers.Int := fun _ _ => Integers.Int.repr 1

theorem cW_ptrs : Ptrs cW := ⟨Or.inr ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩⟩

theorem cW_cells : addr cW.mO 0 = 0 ∧ addr cW.mO 16 = 16 ∧ addr cW.mO 8 = 8 ∧ addr cW.ndlO 0 = 24 ∧ addr cW.ndlO 8 = 32 ∧ addr cW.connO 0 = 40 ∧ addr cW.connO 8 = 48 ∧ addr cW.connO 16 = 56 ∧ addr cW.connO 20 = 60 ∧ addr cW.connO 24 = 64 := by decide

theorem H_cW_satisfiable : ∃ hp, H cW fvW wW hp ∧ Heap.Agrees hp mW := by
  obtain ⟨a0, a16, a8, a24, a32, a40, a48, a56, a60, a64⟩ := cW_cells
  obtain ⟨h1, m1, g1⟩ := cell (chunk := Mptr) (b := bw) (ofs := 0)
    (v := .Vlong (Integers.Int64.repr 0)) (m := mW) (by decide) (by decide)
  obtain ⟨h2, m2, g2⟩ := cell (chunk := .Mint32) (b := bw) (ofs := 16)
    (v := .Vint (Integers.Int.repr 1)) (m := mW) (by decide) (by decide)
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
  obtain ⟨h10, m10, g10⟩ := cell (chunk := .Mint32) (b := bw) (ofs := 64)
    (v := .Vint (Integers.Int.repr 1)) (m := mW) (by decide) (by decide)
  have d1 : Heap.disjoint h1 (Heap.union h2 (Heap.union h3 (Heap.union h4 (Heap.union h5 (Heap.union h6 (Heap.union h7 (Heap.union h8 (Heap.union h9 h10)))))))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m2 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m3 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m4 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m5 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m6 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m7 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m8 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m9 (by decide), mapsto_disj m1 m10 (by decide)⟩⟩⟩⟩⟩⟩⟩⟩
  have d2 : Heap.disjoint h2 (Heap.union h3 (Heap.union h4 (Heap.union h5 (Heap.union h6 (Heap.union h7 (Heap.union h8 (Heap.union h9 h10))))))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m3 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m4 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m5 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m6 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m7 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m8 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m9 (by decide), mapsto_disj m2 m10 (by decide)⟩⟩⟩⟩⟩⟩⟩
  have d3 : Heap.disjoint h3 (Heap.union h4 (Heap.union h5 (Heap.union h6 (Heap.union h7 (Heap.union h8 (Heap.union h9 h10)))))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m4 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m5 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m6 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m7 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m8 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m9 (by decide), mapsto_disj m3 m10 (by decide)⟩⟩⟩⟩⟩⟩
  have d4 : Heap.disjoint h4 (Heap.union h5 (Heap.union h6 (Heap.union h7 (Heap.union h8 (Heap.union h9 h10))))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m5 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m6 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m7 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m8 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m9 (by decide), mapsto_disj m4 m10 (by decide)⟩⟩⟩⟩⟩
  have d5 : Heap.disjoint h5 (Heap.union h6 (Heap.union h7 (Heap.union h8 (Heap.union h9 h10)))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m5 m6 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m5 m7 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m5 m8 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m5 m9 (by decide), mapsto_disj m5 m10 (by decide)⟩⟩⟩⟩
  have d6 : Heap.disjoint h6 (Heap.union h7 (Heap.union h8 (Heap.union h9 h10))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m6 m7 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m6 m8 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m6 m9 (by decide), mapsto_disj m6 m10 (by decide)⟩⟩⟩
  have d7 : Heap.disjoint h7 (Heap.union h8 (Heap.union h9 h10)) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m7 m8 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m7 m9 (by decide), mapsto_disj m7 m10 (by decide)⟩⟩
  have d8 : Heap.disjoint h8 (Heap.union h9 h10) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m8 m9 (by decide), mapsto_disj m8 m10 (by decide)⟩
  have d9 : Heap.disjoint h9 h10 :=
    mapsto_disj m9 m10 (by decide)
  refine ⟨_, ?_, agrees_union g1 (agrees_union g2 (agrees_union g3 (agrees_union g4 (agrees_union g5 (agrees_union g6 (agrees_union g7 (agrees_union g8 (agrees_union g9 g10))))))))⟩
  unfold H
  rw [a0, a16, a8, a24, a32, a40, a48, a56, a60, a64]
  exact ⟨_, _, d1, rfl, m1, _, _, d2, rfl, m2, _, _, d3, rfl, m3, _, _, d4, rfl, m4, _, _, d5, rfl, m5, _, _, d6, rfl, m6, _, _, d7, rfl, m7, _, _, d8, rfl, m8, _, _, d9, rfl, m9, m10⟩

/-- **P0（U0）: 上流の修正前の関数は `ntlmSpec false` を満たし、`mW` の上の入力で、Negotiate 済みで認証情報の違う接続を候補にする（`m->found = conn`）。** -/
theorem P0_C (ge : CGenv) (L : Layout ge.genv_cenv) (X : Deb2026_1965C.TsExt ge cmpW) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_5545_u0.f_url_match_auth_ntlm)
      (ntlmSpec false cW fvW wW cmpW) vs)
    ∧ (∃ hp, H cW fvW wW hp ∧ Heap.Agrees hp mW)
    ∧ bitOf wW 0 = true ∧ Integers.Int.eq cW.hnt Integers.Int.zero = true
    ∧ Integers.Int.eq cW.hns Integers.Int.zero = false
    ∧ Integers.Int.eq (cmpW cW.nu cW.cu) Integers.Int.zero = false
    ∧ vdOf false cW wW cmpW = .candidate :=
  ⟨ntlm_u0 ge cW fvW wW cmpW L rfl rfl cW_ptrs X, H_cW_satisfiable, by decide, by decide, by decide,
   by decide, by decide⟩

/-- **P0（D0）: Debian のパッチの直前の 8.14.1 の関数で、`P0_C` と同じ形。** -/
theorem P0_D (ge : CGenv) (L : Layout ge.genv_cenv) (X : Deb2026_1965C.TsExt ge cmpW) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_5545_d0.f_url_match_auth_ntlm)
      (ntlmSpec false cW fvW wW cmpW) vs)
    ∧ (∃ hp, H cW fvW wW hp ∧ Heap.Agrees hp mW)
    ∧ bitOf wW 0 = true ∧ Integers.Int.eq cW.hnt Integers.Int.zero = true
    ∧ Integers.Int.eq cW.hns Integers.Int.zero = false
    ∧ Integers.Int.eq (cmpW cW.nu cW.cu) Integers.Int.zero = false
    ∧ vdOf false cW wW cmpW = .candidate :=
  ⟨ntlm_d0 ge cW fvW wW cmpW L rfl rfl cW_ptrs X, H_cW_satisfiable, by decide, by decide, by decide,
   by decide, by decide⟩

end Deb2026_5545C
