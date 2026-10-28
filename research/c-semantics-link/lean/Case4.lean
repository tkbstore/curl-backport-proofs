/-
Case 4（CURL-CVE-2025-13034）: C の意味論の上での P1・P0（PROTOCOL §5）。

`Curl_gtls_verifyserver` の戻り値 `r` と H5 のモデルの `verifyserver` を結び付ける仮定（`horacle`）は、
gtls.c が検査を正しく行うという**強い仕様**である（PROTOCOL §4「強い仕様が要る場合は、その旨を記録する」）。
修正が変えたのは「`Curl_gtls_verifyserver` を呼ぶかどうか」だけで、検査の中身は gtls.c にある。
-/
import Case4After
import Case4Before
import Case5Witness
import H5Case4
open CC CC.Sep CC.HProp
open Case5C (addr bitOf cell mapsto_disj agrees_union)

set_option maxRecDepth 20000

namespace Case4C

/-- **P1（C）: 修正後の C 関数は、有効になっている検査のどれかに通らない証明書を受け入れない。**

    `verify_peer_after` により、戻り値は NULL なら 2、そうでなければ `Curl_gtls_verifyserver` の戻り値 `r`。
    `r` が CURLE_OK になるのは H5 の `verifyserver` が真のときだけ（`horacle`）なので、
    `bad` な証明書では戻り値が CURLE_OK にならない。最後の段は H5 の定理 `P1` をそのまま使った。 -/
theorem P1_C (ge : CGenv) (c : Ctx4) (null : Bool) (r : Integers.Int)
    (hcenv : ge.genv_cenv = Case4_after.prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hptr : Ptrs c)
    (bGet bVs : Block) (fdGet fdVs : FunDef)
    (hsGet : Genv.findSymbol ge.genv_genv Case4_after._Curl_ssl_cf_get_primary_config = some bGet)
    (hsVs : Genv.findSymbol ge.genv_genv Case4_after._Curl_gtls_verifyserver = some bVs)
    (hfGet : FuncPtr ge bGet fdGet) (hfVs : FuncPtr ge bVs fdVs)
    (htyGet : typeOfFundef fdGet
      = .Tfunction (getSpec (cpOf c null)).tyargs (getSpec (cpOf c null)).tyres
          (getSpec (cpOf c null)).cc)
    (htyVs : typeOfFundef fdVs = .Tfunction (vsSpec r).tyargs (vsSpec r).tyres (vsSpec r).cc)
    (hGet : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdGet (getSpec (cpOf c null)) vs)
    (hVs : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdVs (vsSpec r) vs)
    (cfg : H5.Case4.Config) (x : H5.Case4.Cert)
    (horacle : Integers.Int.eq r Integers.Int.zero = H5.Case4.verifyserver cfg x) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Case4_after.f_Curl_vquic_tls_verify_peer)
              (vpSpecA c null r) vs)
    ∧ (H5.Case4.bad cfg x = true →
        Integers.Int.eq (if null then Integers.Int.repr 2 else r) Integers.Int.zero = false) :=
  ⟨verify_peer_after ge c null r hcenv hpr hpn hptr bGet bVs fdGet fdVs hsGet hsVs hfGet hfVs
     htyGet htyVs hGet hVs,
   fun hbad => by
     cases null
     · show Integers.Int.eq r Integers.Int.zero = false
       rw [horacle]
       exact H5.Case4.P1 cfg x hbad
     · rfl⟩

/-! ## 前提を満たす具体的なメモリ（1つのブロック、104 バイト）

  オフセット  中身
   0  conn_config の verifyhost を入れた単位 = 0（verifyhost は立っていない）
   8  ctx->gtls.session = NULL
  80  data->set.str[STRING_SSL_PINNEDPUBLICKEY] = ブロックの先頭（公開鍵のピンが設定されている）
  96  peer->scache_key = NULL
-/

def bw4 : Block := Mem.empty.nextblock
def m0_4 : Mem := (Mem.alloc Mem.empty 0 104).1

def storesW4 : Option Mem := do
  let m ← Mem.store .Mint32 m0_4 bw4 0 (.Vint (Integers.Int.repr 0))
  let m ← Mem.store Mptr m bw4 8 (.Vlong (Integers.Int64.repr 0))
  let m ← Mem.store Mptr m bw4 80 (.Vptr bw4 (Integers.Ptrofs.repr 0))
  Mem.store Mptr m bw4 96 (.Vlong (Integers.Int64.repr 0))

theorem storesW4_isSome : storesW4.isSome = true := by decide

def mW4 : Mem := storesW4.get storesW4_isSome

def cW4 : Ctx4 where
  cfV := .Vlong (Integers.Int64.repr 0)
  ctxB := bw4
  ctxO := Integers.Ptrofs.repr 8
  dataB := bw4
  dataO := Integers.Ptrofs.repr 16
  peerB := bw4
  peerO := Integers.Ptrofs.repr 96
  cfgB := bw4
  cfgO := Integers.Ptrofs.repr 0
  word := Integers.Int.repr 0
  sessV := .Vlong (Integers.Int64.repr 0)
  pinV := .Vptr bw4 (Integers.Ptrofs.repr 0)
  keyV := .Vlong (Integers.Int64.repr 0)
  pm := .Freeable

theorem cW4_cells :
    addr cW4.cfgO 0 = 0
    ∧ addr (Integers.Ptrofs.add cW4.ctxO (Integers.Ptrofs.repr 0)) 0 = 8
    ∧ Integers.Ptrofs.unsigned (strOfs cW4.dataO) = 80 ∧ addr cW4.peerO 0 = 96 := by
  decide

theorem cW4_ptrs : Ptrs cW4 :=
  ⟨Or.inr ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩, Or.inl ⟨_, _, rfl⟩, Or.inr ⟨_, rfl⟩⟩

theorem H4_cW4_satisfiable : ∃ hp, H4 cW4 hp ∧ Heap.Agrees hp mW4 := by
  obtain ⟨a0, a8, a80, a96⟩ := cW4_cells
  obtain ⟨h1, m1, g1⟩ := cell (chunk := .Mint32) (b := bw4) (ofs := 0)
    (v := .Vint (Integers.Int.repr 0)) (m := mW4) (by decide) (by decide)
  obtain ⟨h2, m2, g2⟩ := cell (chunk := Mptr) (b := bw4) (ofs := 8)
    (v := .Vlong (Integers.Int64.repr 0)) (m := mW4) (by decide) (by decide)
  obtain ⟨h3, m3, g3⟩ := cell (chunk := Mptr) (b := bw4) (ofs := 80)
    (v := .Vptr bw4 (Integers.Ptrofs.repr 0)) (m := mW4) (by decide) (by decide)
  obtain ⟨h4, m4, g4⟩ := cell (chunk := Mptr) (b := bw4) (ofs := 96)
    (v := .Vlong (Integers.Int64.repr 0)) (m := mW4) (by decide) (by decide)
  have d34 := mapsto_disj m3 m4 (by decide)
  have d2 : Heap.disjoint h2 (Heap.union h3 h4) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m3 (by decide), mapsto_disj m2 m4 (by decide)⟩
  have d1 : Heap.disjoint h1 (Heap.union h2 (Heap.union h3 h4)) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m2 (by decide),
      Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m3 (by decide), mapsto_disj m1 m4 (by decide)⟩⟩
  refine ⟨_, ?_, agrees_union g1 (agrees_union g2 (agrees_union g3 g4))⟩
  unfold H4
  rw [a0, a8, a80, a96]
  exact ⟨_, _, d1, rfl, m1, _, _, d2, rfl, m2, _, _, d34, rfl, m3, m4⟩

/-- **P0（C）: 修正前の C 関数には、脆弱性が起きる入力がある。**

    H5 の反例（ホスト名の検証を切り、公開鍵のピンを設定した接続に、ピンの合わない証明書）を、
    具体的なメモリ `mW4` の上の値 `cW4` で与える。`Curl_gtls_verifyserver` は拒否する（`r = 1`）が、
    修正前の関数は verifyhost が立っていないので呼ばず、CURLE_OK を返す。 -/
theorem P0_C :
    ∃ (c : Ctx4) (cfg : H5.Case4.Config) (x : H5.Case4.Cert) (r : Integers.Int),
      (∃ hp m, H4 c hp ∧ Heap.Agrees hp m)
      ∧ permOrder c.pm .Readable = true ∧ permOrder c.pm .Nonempty = true ∧ Ptrs c
      ∧ cfg.verifyhost = bitOf c.word 0
      ∧ Integers.Int.eq r Integers.Int.zero = H5.Case4.verifyserver cfg x
      ∧ H5.Case4.bad cfg x = true
      ∧ Integers.Int.eq (if bitOf c.word 0 then r else Integers.Int.repr 0) Integers.Int.zero
          = true
      ∧ ∀ (ge : CGenv) (bGet bVs : Block) (fdGet fdVs : FunDef),
          ge.genv_cenv = Case4_before.prog.prog_comp_env →
          Genv.findSymbol ge.genv_genv Case4_before._Curl_ssl_cf_get_primary_config = some bGet →
          Genv.findSymbol ge.genv_genv Case4_before._Curl_gtls_verifyserver = some bVs →
          FuncPtr ge bGet fdGet → FuncPtr ge bVs fdVs →
          typeOfFundef fdGet = .Tfunction (getSpec (cpOf c false)).tyargs
            (getSpec (cpOf c false)).tyres (getSpec (cpOf c false)).cc →
          typeOfFundef fdVs = .Tfunction (vsSpec r).tyargs (vsSpec r).tyres (vsSpec r).cc →
          (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdGet (getSpec (cpOf c false)) vs) →
          (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdVs (vsSpec r) vs) →
          ∀ vs, SatisfiesAt ge (FunctionEntry2 ge)
            (.Internal Case4_before.f_Curl_vquic_tls_verify_peer) (vpSpecB c false r) vs := by
  obtain ⟨hp, hH, hag⟩ := H4_cW4_satisfiable
  refine ⟨cW4, ⟨false, false, true⟩, ⟨true, true, false⟩, Integers.Int.repr 1,
    ⟨hp, mW4, hH, hag⟩, rfl, rfl, cW4_ptrs, by decide, by decide, by decide, by decide, ?_⟩
  intro ge bGet bVs fdGet fdVs hcenv hsGet hsVs hfGet hfVs htyGet htyVs hGet hVs vs
  exact verify_peer_before ge cW4 false _ hcenv rfl rfl cW4_ptrs bGet bVs fdGet fdVs hsGet hsVs
    hfGet hfVs htyGet htyVs hGet hVs vs

end Case4C

#print axioms Case4C.P1_C
#print axioms Case4C.P0_C
#print axioms Case4C.verify_peer_after
#print axioms Case4C.verify_peer_before
#print axioms Case4C.H4_cW4_satisfiable
