/-
CVE-2026-8286: C の意味論の上での P1・P0（`research/backport-proof-debian/cases/CVE-2026-8286.md`）。

- P1（U1・D1）: `may_tls` が 1 で `Curl_ssl_conn_config_match` が偽なら、`url_match_ssl_config` は FALSE を返し、
  照合の判定（`url_match_ssl_use` かつ `url_match_ssl_config`）は偽
- P0（U0・D0）: 具体的なメモリ `mW` の上に前提を満たすヒープがあり、その入力（STARTTLS の scheme、TLS の接続、
  `may_tls` が 1、`req_tls` が 0、設定が合わない）で、2つの関数はどちらも TRUE を返す
-/
import Deb2026_8286U1
import Deb2026_8286U0
import Deb2026_8286D1
import Deb2026_8286D0
import Case5Witness
open CC CC.Sep CC.HProp
open Case5C (addr flagBit bitOf cell mapsto_disj agrees_union)

set_option maxRecDepth 20000

namespace Deb2026_8286C

/-- 戻り値の上での P1（`reuse` は U と D で違ってよい）。 -/
theorem p1_ret (reuse : Bool) (c : Ctx) (ssl cfg : Bool) :
    bitOf c.word 0 = true → cfg = false → (useRet reuse 1 c ssl && cfgRet true c cfg) = false := by
  intro h1 h2
  subst h2
  simp [cfgRet, h1]

/-- **P1（U1）: 上流の修正後の2つの関数は仕様を満たし、TLS に上げうる転送は設定の違う接続を再利用しない。** -/
theorem P1_C (ge : CGenv) (c : Ctx) (ssl cfg : Bool)
    (L : Layout ge.genv_cenv "Curl_scheme" "scheme")
    (hpr : permOrder c.pm .Readable = true)
    (XS : SslExt ge c ssl) (XC : CfgExt ge c cfg) (bG : Block)
    (hsG : Genv.findSymbol ge.genv_genv (identOfString "get_protocol_family") = some bG)
    (hfG : FuncPtr ge bG (.Internal Deb2026_8286_u1.f_get_protocol_family)) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_8286_u1.f_url_match_ssl_use)
      (useSpec true 1 c ssl) vs)
    ∧ (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_8286_u1.f_url_match_ssl_config)
      (confSpec true c cfg) vs)
    ∧ (bitOf c.word 0 = true → cfg = false →
        (useRet true 1 c ssl && cfgRet true c cfg) = false) :=
  ⟨use_u1 ge c ssl L hpr XS bG hsG hfG, cfg_u1 ge c cfg L hpr XC, p1_ret true c ssl cfg⟩

/-- **P1（D1）: 8.14.1 に Debian のパッチを当てた関数で、`P1_C` と同じ形（`reuse` だけが違う）。** -/
theorem P1_D (ge : CGenv) (c : Ctx) (ssl cfg : Bool)
    (L : Layout ge.genv_cenv "Curl_handler" "handler")
    (hpr : permOrder c.pm .Readable = true)
    (XS : SslExt ge c ssl) (XC : CfgExt ge c cfg) (bG : Block)
    (hsG : Genv.findSymbol ge.genv_genv (identOfString "get_protocol_family") = some bG)
    (hfG : FuncPtr ge bG (.Internal Deb2026_8286_d1.f_get_protocol_family)) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_8286_d1.f_url_match_ssl_use)
      (useSpec false 1 c ssl) vs)
    ∧ (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_8286_d1.f_url_match_ssl_config)
      (confSpec true c cfg) vs)
    ∧ (bitOf c.word 0 = true → cfg = false →
        (useRet false 1 c ssl && cfgRet true c cfg) = false) :=
  ⟨use_d1 ge c ssl L hpr XS bG hsG hfG, cfg_d1 ge c cfg L hpr XC, p1_ret false c ssl cfg⟩

/-! ## 前提を満たす具体的なメモリ（1つのブロック、80 バイト）

  オフセット  中身
   0  m->data = ブロックの先頭、8  m->needle = 24、16  m の単位 = 1（may_tls だけが 1。req_tls は 0）
  24  needle->scheme = 32、32  protocol = 1、48  flags = 32768（PROTOPT_SSL_REUSE。PROTOPT_SSL は立っていない）
  56  conn->scheme = 64、72  family = 1
  `Curl_conn_is_ssl` は真（接続は TLS）、`Curl_ssl_conn_config_match` は偽（設定が合わない）
-/

def bw : Block := Mem.empty.nextblock
def m0 : Mem := (Mem.alloc Mem.empty 0 80).1
def ptr (o : Nat) : Val := .Vptr bw (Integers.Ptrofs.repr o)

def storesW : Option Mem := do
  let m ← Mem.store Mptr m0 bw 0 (ptr 0)
  let m ← Mem.store Mptr m bw 8 (ptr 24)
  let m ← Mem.store .Mint32 m bw 16 (.Vint (Integers.Int.repr 1))
  let m ← Mem.store Mptr m bw 24 (ptr 32)
  let m ← Mem.store .Mint64 m bw 32 (.Vlong (Integers.Int64.repr 1))
  let m ← Mem.store .Mint32 m bw 48 (.Vint (Integers.Int.repr 32768))
  let m ← Mem.store Mptr m bw 56 (ptr 64)
  Mem.store .Mint64 m bw 72 (.Vlong (Integers.Int64.repr 1))

theorem storesW_isSome : storesW.isSome = true := by decide

def mW : Mem := storesW.get storesW_isSome

def cW : Ctx where
  connB := bw
  connO := Integers.Ptrofs.repr 56
  mB := bw
  mO := Integers.Ptrofs.repr 0
  dataB := bw
  dataO := Integers.Ptrofs.repr 0
  ndlB := bw
  ndlO := Integers.Ptrofs.repr 24
  nschB := bw
  nschO := Integers.Ptrofs.repr 32
  cschB := bw
  cschO := Integers.Ptrofs.repr 64
  word := Integers.Int.repr 1
  flags := Integers.Int.repr 32768
  proto := Integers.Int64.repr 1
  fam := Integers.Int64.repr 1
  pm := .Freeable

theorem cW_cells : addr cW.mO 0 = 0 ∧ addr cW.mO 8 = 8 ∧ addr cW.mO 16 = 16 ∧ addr cW.ndlO 0 = 24 ∧ addr cW.nschO 0 = 32 ∧ addr cW.nschO 16 = 48 ∧ addr cW.connO 0 = 56 ∧ addr cW.cschO 8 = 72 := by decide

theorem H_cW_satisfiable : ∃ hp, H cW hp ∧ Heap.Agrees hp mW := by
  obtain ⟨a0, a8, a16, a24, a32, a48, a56, a72⟩ := cW_cells
  obtain ⟨h1, m1, g1⟩ := cell (chunk := Mptr) (b := bw) (ofs := 0)
    (v := ptr 0) (m := mW) (by decide) (by decide)
  obtain ⟨h2, m2, g2⟩ := cell (chunk := Mptr) (b := bw) (ofs := 8)
    (v := ptr 24) (m := mW) (by decide) (by decide)
  obtain ⟨h3, m3, g3⟩ := cell (chunk := .Mint32) (b := bw) (ofs := 16)
    (v := .Vint (Integers.Int.repr 1)) (m := mW) (by decide) (by decide)
  obtain ⟨h4, m4, g4⟩ := cell (chunk := Mptr) (b := bw) (ofs := 24)
    (v := ptr 32) (m := mW) (by decide) (by decide)
  obtain ⟨h5, m5, g5⟩ := cell (chunk := .Mint64) (b := bw) (ofs := 32)
    (v := .Vlong (Integers.Int64.repr 1)) (m := mW) (by decide) (by decide)
  obtain ⟨h6, m6, g6⟩ := cell (chunk := .Mint32) (b := bw) (ofs := 48)
    (v := .Vint (Integers.Int.repr 32768)) (m := mW) (by decide) (by decide)
  obtain ⟨h7, m7, g7⟩ := cell (chunk := Mptr) (b := bw) (ofs := 56)
    (v := ptr 64) (m := mW) (by decide) (by decide)
  obtain ⟨h8, m8, g8⟩ := cell (chunk := .Mint64) (b := bw) (ofs := 72)
    (v := .Vlong (Integers.Int64.repr 1)) (m := mW) (by decide) (by decide)
  have d1 : Heap.disjoint h1 (Heap.union h2 (Heap.union h3 (Heap.union h4 (Heap.union h5 (Heap.union h6 (Heap.union h7 h8)))))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m2 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m3 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m4 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m5 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m6 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m7 (by decide), mapsto_disj m1 m8 (by decide)⟩⟩⟩⟩⟩⟩
  have d2 : Heap.disjoint h2 (Heap.union h3 (Heap.union h4 (Heap.union h5 (Heap.union h6 (Heap.union h7 h8))))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m3 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m4 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m5 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m6 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m7 (by decide), mapsto_disj m2 m8 (by decide)⟩⟩⟩⟩⟩
  have d3 : Heap.disjoint h3 (Heap.union h4 (Heap.union h5 (Heap.union h6 (Heap.union h7 h8)))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m4 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m5 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m6 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m7 (by decide), mapsto_disj m3 m8 (by decide)⟩⟩⟩⟩
  have d4 : Heap.disjoint h4 (Heap.union h5 (Heap.union h6 (Heap.union h7 h8))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m5 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m6 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m7 (by decide), mapsto_disj m4 m8 (by decide)⟩⟩⟩
  have d5 : Heap.disjoint h5 (Heap.union h6 (Heap.union h7 h8)) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m5 m6 (by decide), Heap.disjoint_union_right.mpr ⟨mapsto_disj m5 m7 (by decide), mapsto_disj m5 m8 (by decide)⟩⟩
  have d6 : Heap.disjoint h6 (Heap.union h7 h8) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m6 m7 (by decide), mapsto_disj m6 m8 (by decide)⟩
  have d7 : Heap.disjoint h7 h8 :=
    mapsto_disj m7 m8 (by decide)
  refine ⟨_, ?_, agrees_union g1 (agrees_union g2 (agrees_union g3 (agrees_union g4 (agrees_union g5 (agrees_union g6 (agrees_union g7 g8))))))⟩
  unfold H
  rw [a0, a8, a16, a24, a32, a48, a56, a72]
  exact ⟨_, _, d1, rfl, m1, _, _, d2, rfl, m2, _, _, d3, rfl, m3, _, _, d4, rfl, m4, _, _, d5, rfl, m5, _, _, d6, rfl, m6, _, _, d7, rfl, m7, m8⟩

/-- **P0（U0）: 上流の修正前の2つの関数は仕様を満たし、`mW` の上の入力で、TLS に上げうる転送が設定の違う TLS の接続を再利用する（どちらも TRUE）。** -/
theorem P0_C (ge : CGenv) (L : Layout ge.genv_cenv "Curl_scheme" "scheme")
    (XS : SslExt ge cW true) (XC : CfgExt ge cW false) (bG : Block)
    (hsG : Genv.findSymbol ge.genv_genv (identOfString "get_protocol_family") = some bG)
    (hfG : FuncPtr ge bG (.Internal Deb2026_8286_u0.f_get_protocol_family)) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_8286_u0.f_url_match_ssl_use)
      (useSpec true 2 cW true) vs)
    ∧ (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_8286_u0.f_url_match_ssl_config)
      (confSpec false cW false) vs)
    ∧ (∃ hp, H cW hp ∧ Heap.Agrees hp mW)
    ∧ flagBit cW.flags 0 = false ∧ bitOf cW.word 0 = true ∧ bitOf cW.word 2 = false
    ∧ useRet true 2 cW true = true ∧ cfgRet false cW false = true :=
  ⟨use_u0 ge cW true L rfl XS bG hsG hfG, cfg_u0 ge cW false L rfl XC, H_cW_satisfiable,
   by decide, by decide, by decide, by decide, by decide⟩

/-- **P0（D0）: Debian のパッチの直前の 8.14.1 の関数で、`P0_C` と同じ形。** -/
theorem P0_D (ge : CGenv) (L : Layout ge.genv_cenv "Curl_handler" "handler")
    (XS : SslExt ge cW true) (XC : CfgExt ge cW false) (bG : Block)
    (hsG : Genv.findSymbol ge.genv_genv (identOfString "get_protocol_family") = some bG)
    (hfG : FuncPtr ge bG (.Internal Deb2026_8286_d0.f_get_protocol_family)) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_8286_d0.f_url_match_ssl_use)
      (useSpec false 2 cW true) vs)
    ∧ (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_8286_d0.f_url_match_ssl_config)
      (confSpec false cW false) vs)
    ∧ (∃ hp, H cW hp ∧ Heap.Agrees hp mW)
    ∧ flagBit cW.flags 0 = false ∧ bitOf cW.word 0 = true ∧ bitOf cW.word 2 = false
    ∧ useRet false 2 cW true = true ∧ cfgRet false cW false = true :=
  ⟨use_d0 ge cW true L rfl XS bG hsG hfG, cfg_d0 ge cW false L rfl XC, H_cW_satisfiable,
   by decide, by decide, by decide, by decide, by decide⟩

end Deb2026_8286C
