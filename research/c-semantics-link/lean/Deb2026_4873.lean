/-
CVE-2026-4873: C の意味論の上での P1・P0（`research/backport-proof-debian/cases/CVE-2026-4873.md`）。

- P1（U1・D1）: 要求する scheme が TLS でなく、接続が TLS でなく（`Curl_conn_is_ssl` が偽）、`req_tls` が 1 なら FALSE を返す
- P0（U0・D0）: 具体的なメモリ `mW` の上に前提を満たすヒープがあり、その入力（scheme が TLS でない、接続が TLS でない、
  `req_tls` が 1）で TRUE を返す（TLS を要求する転送が平文の接続を再利用する）
-/
import Deb2026_4873U1
import Deb2026_4873U0
import Deb2026_4873D1
import Deb2026_4873D0
import Case5Witness
open CC CC.Sep CC.HProp
open Case5C (addr flagBit bitOf cell mapsto_disj agrees_union)

set_option maxRecDepth 20000

namespace Deb2026_4873C

/-- 戻り値の上での P1（`reuse` は U と D で違ってよい。`req = true` の版だけが成り立つ）。 -/
theorem p1_ret (reuse : Bool) (c : Ctx) (ssl : Bool) :
    flagBit c.flags 0 = false → ssl = false → bitOf c.word 0 = true → retOf reuse true c ssl = false := by
  intro h1 h2 h3
  simp [retOf, ret, h1, h2, h3]

/-- **P1（U1）: 上流の修正後の関数は `useSpec true true` を満たし、TLS を要求する転送に平文の接続を使わない。** -/
theorem P1_C (ge : CGenv) (c : Ctx) (ssl : Bool)
    (L : Layout ge.genv_cenv "Curl_scheme" "scheme")
    (hpr : permOrder c.pm .Readable = true)
    (XS : SslExt ge c ssl) (bG : Block)
    (hsG : Genv.findSymbol ge.genv_genv (identOfString "get_protocol_family") = some bG)
    (hfG : FuncPtr ge bG (.Internal Deb2026_4873_u1.f_get_protocol_family)) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_4873_u1.f_url_match_ssl_use)
      (useSpec true true c ssl) vs)
    ∧ (flagBit c.flags 0 = false → ssl = false → bitOf c.word 0 = true → retOf true true c ssl = false) :=
  ⟨use_u1 ge c ssl L hpr XS bG hsG hfG, p1_ret true c ssl⟩

/-- **P1（D1）: 8.14.1 に Debian のパッチを当てた関数で、`P1_C` と同じ形（`reuse` だけが違う）。** -/
theorem P1_D (ge : CGenv) (c : Ctx) (ssl : Bool)
    (L : Layout ge.genv_cenv "Curl_handler" "handler")
    (hpr : permOrder c.pm .Readable = true)
    (XS : SslExt ge c ssl) (bG : Block)
    (hsG : Genv.findSymbol ge.genv_genv (identOfString "get_protocol_family") = some bG)
    (hfG : FuncPtr ge bG (.Internal Deb2026_4873_d1.f_get_protocol_family)) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_4873_d1.f_url_match_ssl_use)
      (useSpec false true c ssl) vs)
    ∧ (flagBit c.flags 0 = false → ssl = false → bitOf c.word 0 = true → retOf false true c ssl = false) :=
  ⟨use_d1 ge c ssl L hpr XS bG hsG hfG, p1_ret false c ssl⟩

/-! ## 前提を満たす具体的なメモリ（1つのブロック、72 バイト）

  オフセット  中身
   0  m->needle = 16、8  m の単位 = 1（req_tls）
  16  needle->scheme = 24、24  protocol = 1、40  flags = 0（PROTOPT_SSL が立っていない）
  48  conn->scheme = 56、64  family = 1
-/

def bw : Block := Mem.empty.nextblock
def m0 : Mem := (Mem.alloc Mem.empty 0 72).1
def ptr (o : Nat) : Val := .Vptr bw (Integers.Ptrofs.repr o)

def storesW : Option Mem := do
  let m ← Mem.store Mptr m0 bw 0 (ptr 16)
  let m ← Mem.store .Mint32 m bw 8 (.Vint (Integers.Int.repr 1))
  let m ← Mem.store Mptr m bw 16 (ptr 24)
  let m ← Mem.store .Mint64 m bw 24 (.Vlong (Integers.Int64.repr 1))
  let m ← Mem.store .Mint32 m bw 40 (.Vint (Integers.Int.repr 0))
  let m ← Mem.store Mptr m bw 48 (ptr 56)
  Mem.store .Mint64 m bw 64 (.Vlong (Integers.Int64.repr 1))

theorem storesW_isSome : storesW.isSome = true := by decide

def mW : Mem := storesW.get storesW_isSome

def cW : Ctx where
  connB := bw
  connO := Integers.Ptrofs.repr 48
  mB := bw
  mO := Integers.Ptrofs.repr 0
  ndlB := bw
  ndlO := Integers.Ptrofs.repr 16
  nschB := bw
  nschO := Integers.Ptrofs.repr 24
  cschB := bw
  cschO := Integers.Ptrofs.repr 56
  word := Integers.Int.repr 1
  flags := Integers.Int.repr 0
  proto := Integers.Int64.repr 1
  fam := Integers.Int64.repr 1
  pm := .Freeable

theorem cW_cells : addr cW.mO 0 = 0 ∧ addr cW.mO 8 = 8 ∧ addr cW.ndlO 0 = 16 ∧ addr cW.nschO 0 = 24 ∧ addr cW.nschO 16 = 40 ∧ addr cW.connO 0 = 48 ∧ addr cW.cschO 8 = 64 := by decide

theorem H_cW_satisfiable : ∃ hp, H cW hp ∧ Heap.Agrees hp mW := by
  obtain ⟨a0, a8, a16, a24, a40, a48, a64⟩ := cW_cells
  obtain ⟨h1, m1, g1⟩ := cell (chunk := Mptr) (b := bw) (ofs := 0)
    (v := ptr 16) (m := mW) (by decide) (by decide)
  obtain ⟨h2, m2, g2⟩ := cell (chunk := .Mint32) (b := bw) (ofs := 8)
    (v := .Vint (Integers.Int.repr 1)) (m := mW) (by decide) (by decide)
  obtain ⟨h3, m3, g3⟩ := cell (chunk := Mptr) (b := bw) (ofs := 16)
    (v := ptr 24) (m := mW) (by decide) (by decide)
  obtain ⟨h4, m4, g4⟩ := cell (chunk := .Mint64) (b := bw) (ofs := 24)
    (v := .Vlong (Integers.Int64.repr 1)) (m := mW) (by decide) (by decide)
  obtain ⟨h5, m5, g5⟩ := cell (chunk := .Mint32) (b := bw) (ofs := 40)
    (v := .Vint (Integers.Int.repr 0)) (m := mW) (by decide) (by decide)
  obtain ⟨h6, m6, g6⟩ := cell (chunk := Mptr) (b := bw) (ofs := 48)
    (v := ptr 56) (m := mW) (by decide) (by decide)
  obtain ⟨h7, m7, g7⟩ := cell (chunk := .Mint64) (b := bw) (ofs := 64)
    (v := .Vlong (Integers.Int64.repr 1)) (m := mW) (by decide) (by decide)
  have d1 : Heap.disjoint h1 (Heap.union h2 (Heap.union h3 (Heap.union h4 (Heap.union h5 (Heap.union h6 h7))))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m2 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m3 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m4 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m5 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m6 (by decide), mapsto_disj m1 m7 (by decide)⟩⟩⟩⟩⟩
  have d2 : Heap.disjoint h2 (Heap.union h3 (Heap.union h4 (Heap.union h5 (Heap.union h6 h7)))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m3 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m4 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m5 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m6 (by decide), mapsto_disj m2 m7 (by decide)⟩⟩⟩⟩
  have d3 : Heap.disjoint h3 (Heap.union h4 (Heap.union h5 (Heap.union h6 h7))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m4 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m5 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m6 (by decide), mapsto_disj m3 m7 (by decide)⟩⟩⟩
  have d4 : Heap.disjoint h4 (Heap.union h5 (Heap.union h6 h7)) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m5 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m6 (by decide), mapsto_disj m4 m7 (by decide)⟩⟩
  have d5 : Heap.disjoint h5 (Heap.union h6 h7) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m5 m6 (by decide), mapsto_disj m5 m7 (by decide)⟩
  have d6 : Heap.disjoint h6 h7 :=
    mapsto_disj m6 m7 (by decide)
  refine ⟨_, ?_, agrees_union g1 (agrees_union g2 (agrees_union g3 (agrees_union g4 (agrees_union g5 (agrees_union g6 g7)))))⟩
  unfold H
  rw [a0, a8, a16, a24, a40, a48, a64]
  exact ⟨_, _, d1, rfl, m1, _, _, d2, rfl, m2, _, _, d3, rfl, m3, _, _, d4, rfl, m4, _, _, d5, rfl, m5, _, _, d6, rfl, m6, m7⟩

/-- **P0（U0）: 上流の修正前の関数は `useSpec true false` を満たし、`mW` の上の入力で、TLS を要求する転送が平文の接続を再利用する（TRUE）。** -/
theorem P0_C (ge : CGenv) (L : Layout ge.genv_cenv "Curl_scheme" "scheme") (XS : SslExt ge cW false) (bG : Block)
    (hsG : Genv.findSymbol ge.genv_genv (identOfString "get_protocol_family") = some bG)
    (hfG : FuncPtr ge bG (.Internal Deb2026_4873_u0.f_get_protocol_family)) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_4873_u0.f_url_match_ssl_use)
      (useSpec true false cW false) vs)
    ∧ (∃ hp, H cW hp ∧ Heap.Agrees hp mW)
    ∧ flagBit cW.flags 0 = false ∧ bitOf cW.word 0 = true ∧ retOf true false cW false = true :=
  ⟨use_u0 ge cW false L rfl XS bG hsG hfG, H_cW_satisfiable, by decide, by decide, by decide⟩

/-- **P0（D0）: Debian のパッチの直前の 8.14.1 の関数で、`P0_C` と同じ形。** -/
theorem P0_D (ge : CGenv) (L : Layout ge.genv_cenv "Curl_handler" "handler") (XS : SslExt ge cW false) (bG : Block)
    (hsG : Genv.findSymbol ge.genv_genv (identOfString "get_protocol_family") = some bG)
    (hfG : FuncPtr ge bG (.Internal Deb2026_4873_d0.f_get_protocol_family)) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_4873_d0.f_url_match_ssl_use)
      (useSpec false false cW false) vs)
    ∧ (∃ hp, H cW hp ∧ Heap.Agrees hp mW)
    ∧ flagBit cW.flags 0 = false ∧ bitOf cW.word 0 = true ∧ retOf false false cW false = true :=
  ⟨use_d0 ge cW false L rfl XS bG hsG hfG, H_cW_satisfiable, by decide, by decide, by decide⟩

end Deb2026_4873C
