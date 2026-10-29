/-
CVE-2025-13034 trixie: 上流の修正後（U1、3d91ca8cdb）・修正前（U0、dc34498d18）の `Curl_vquic_tls_verify_peer` の上の P1・P0。

上流の2つのコミットは C1 の Case 4 と同じである。この件の翻訳単位（`debtrixie2025_13034/`）から生成した Clight の関数と構造体の環境は、
Case 4 の翻訳単位から生成したものと同じ構文木になる（`fn_u1_same` など、`rfl`。生成した Lean の違いは `Info.source_file` だけ）。
そのため Case 4 で証明した `Case4C.P1_C`・`Case4C.P0_C` を、等式で書き換えてこの件の関数の上の定理にする。
-/
import GenDebTrixie2025_13034U1
import GenDebTrixie2025_13034U0
import Case4
open CC CC.Sep CC.HProp
open Case5C (bitOf)

set_option maxRecDepth 20000

namespace DebTrixie2025_13034C
open Case4C

theorem fn_u1_same : DebTrixie2025_13034_u1.f_Curl_vquic_tls_verify_peer
    = Case4_after.f_Curl_vquic_tls_verify_peer := rfl
theorem cenv_u1_same : DebTrixie2025_13034_u1.prog.prog_comp_env
    = Case4_after.prog.prog_comp_env := rfl
theorem fn_u0_same : DebTrixie2025_13034_u0.f_Curl_vquic_tls_verify_peer
    = Case4_before.f_Curl_vquic_tls_verify_peer := rfl
theorem cenv_u0_same : DebTrixie2025_13034_u0.prog.prog_comp_env
    = Case4_before.prog.prog_comp_env := rfl

/-- **U1（P1）**: 上流の修正後の関数は、有効になっている検査のどれかに通らない証明書を受け入れない。 -/
theorem P1_U1 (ge : CGenv) (c : Ctx4) (null : Bool) (r : Integers.Int)
    (hcenv : ge.genv_cenv = DebTrixie2025_13034_u1.prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hptr : Ptrs c)
    (bGet bVs : Block) (fdGet fdVs : FunDef)
    (hsGet : Genv.findSymbol ge.genv_genv DebTrixie2025_13034_u1._Curl_ssl_cf_get_primary_config = some bGet)
    (hsVs : Genv.findSymbol ge.genv_genv DebTrixie2025_13034_u1._Curl_gtls_verifyserver = some bVs)
    (hfGet : FuncPtr ge bGet fdGet) (hfVs : FuncPtr ge bVs fdVs)
    (htyGet : typeOfFundef fdGet
      = .Tfunction (getSpec (cpOf c null)).tyargs (getSpec (cpOf c null)).tyres
          (getSpec (cpOf c null)).cc)
    (htyVs : typeOfFundef fdVs = .Tfunction (vsSpec r).tyargs (vsSpec r).tyres (vsSpec r).cc)
    (hGet : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdGet (getSpec (cpOf c null)) vs)
    (hVs : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdVs (vsSpec r) vs)
    (cfg : H5.Case4.Config) (x : H5.Case4.Cert)
    (horacle : Integers.Int.eq r Integers.Int.zero = H5.Case4.verifyserver cfg x) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge)
              (.Internal DebTrixie2025_13034_u1.f_Curl_vquic_tls_verify_peer) (vpSpecA c null r) vs)
    ∧ (H5.Case4.bad cfg x = true →
        Integers.Int.eq (if null then Integers.Int.repr 2 else r) Integers.Int.zero = false) := by
  rw [fn_u1_same]
  exact Case4C.P1_C ge c null r (hcenv.trans cenv_u1_same) hpr hpn hptr bGet bVs fdGet fdVs
    hsGet hsVs hfGet hfVs htyGet htyVs hGet hVs cfg x horacle

/-- **U0（P0）**: 上流の修正前の関数には、ピンの合わない証明書を受け入れる入力がある。 -/
theorem P0_U0 :
    ∃ (c : Ctx4) (cfg : H5.Case4.Config) (x : H5.Case4.Cert) (r : Integers.Int),
      (∃ hp m, H4 c hp ∧ Heap.Agrees hp m)
      ∧ permOrder c.pm .Readable = true ∧ permOrder c.pm .Nonempty = true ∧ Ptrs c
      ∧ cfg.verifyhost = bitOf c.word 0
      ∧ Integers.Int.eq r Integers.Int.zero = H5.Case4.verifyserver cfg x
      ∧ H5.Case4.bad cfg x = true
      ∧ Integers.Int.eq (if bitOf c.word 0 then r else Integers.Int.repr 0) Integers.Int.zero
          = true
      ∧ ∀ (ge : CGenv) (bGet bVs : Block) (fdGet fdVs : FunDef),
          ge.genv_cenv = DebTrixie2025_13034_u0.prog.prog_comp_env →
          Genv.findSymbol ge.genv_genv DebTrixie2025_13034_u0._Curl_ssl_cf_get_primary_config
            = some bGet →
          Genv.findSymbol ge.genv_genv DebTrixie2025_13034_u0._Curl_gtls_verifyserver = some bVs →
          FuncPtr ge bGet fdGet → FuncPtr ge bVs fdVs →
          typeOfFundef fdGet = .Tfunction (getSpec (cpOf c false)).tyargs
            (getSpec (cpOf c false)).tyres (getSpec (cpOf c false)).cc →
          typeOfFundef fdVs = .Tfunction (vsSpec r).tyargs (vsSpec r).tyres (vsSpec r).cc →
          (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdGet (getSpec (cpOf c false)) vs) →
          (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdVs (vsSpec r) vs) →
          ∀ vs, SatisfiesAt ge (FunctionEntry2 ge)
            (.Internal DebTrixie2025_13034_u0.f_Curl_vquic_tls_verify_peer) (vpSpecB c false r) vs := by
  obtain ⟨c, cfg, x, r, hsat, hpr, hpn, hptr, hvh, hor, hbad, hev, h⟩ := Case4C.P0_C
  refine ⟨c, cfg, x, r, hsat, hpr, hpn, hptr, hvh, hor, hbad, hev, ?_⟩
  intro ge bGet bVs fdGet fdVs hcenv hsGet hsVs hfGet hfVs htyGet htyVs hGet hVs vs
  rw [fn_u0_same]
  exact h ge bGet bVs fdGet fdVs (hcenv.trans cenv_u0_same) hsGet hsVs hfGet hfVs htyGet htyVs
    hGet hVs vs

end DebTrixie2025_13034C

#print axioms DebTrixie2025_13034C.P1_U1
#print axioms DebTrixie2025_13034C.P0_U0
