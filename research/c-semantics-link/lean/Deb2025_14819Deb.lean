/-
CVE-2025-14819: Debian のバックポート（D1: curl 8.14.1 に CVE-2025-14819.patch を当てたもの、D0: 8.14.1）の上の P1・P0。

前置きで構造体を関数が触るフィールドだけに減らすと、Debian の翻訳単位から生成した Clight の関数は、上流の翻訳単位から生成したものと
同じ構文木になる（`fn_*_same`、`rfl`）。構造体の環境も同じ（`cenv_*_same`）。そのため U1・U0 の定理を、そのまま D1・D0 の関数の上の定理に移せる。
-/
import GenDeb2025_14819DebAfter
import GenDeb2025_14819DebBefore
import Deb2025_14819After
import Deb2025_14819Before
open CC CC.Sep CC.HProp
open Case5C (bitOf)
open Case4debC (IsPtr)

set_option maxRecDepth 20000

namespace Deb2025_14819DC
open Deb2025_14819C

theorem fn_after_same : Deb2025_14819_deb_after.f_ossl_cached_x509_store_different
    = Deb2025_14819_up_after.f_ossl_cached_x509_store_different := rfl
theorem cenv_after_same : Deb2025_14819_deb_after.prog.prog_comp_env
    = Deb2025_14819_up_after.prog.prog_comp_env := rfl
theorem fn_before_same : Deb2025_14819_deb_before.f_ossl_cached_x509_store_different
    = Deb2025_14819_up_before.f_ossl_cached_x509_store_different := rfl
theorem cenv_before_same : Deb2025_14819_deb_before.prog.prog_comp_env
    = Deb2025_14819_up_before.prog.prog_comp_env := rfl

/-- **D1（P1）**: Debian のバックポートを当てた 8.14.1 の関数は、記録された `no_partialchain` と今の設定が違えば TRUE を返す。 -/
theorem different_debian (ge : CGenv) (c : Ctx)
    (hcenv : ge.genv_cenv = Deb2025_14819_deb_after.prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hcf : IsPtr c.cfV)
    (hne : bitOf c.mbWord 0 ≠ bitOf c.cfgWord 0)
    (bGet bCfg : Block) (fdGet fdCfg : FunDef)
    (hsGet : Genv.findSymbol ge.genv_genv Deb2025_14819_deb_after._Curl_ssl_cf_get_primary_config = some bGet)
    (hsCfg : Genv.findSymbol ge.genv_genv Deb2025_14819_deb_after._Curl_ssl_cf_get_config = some bCfg)
    (hfGet : FuncPtr ge bGet fdGet) (hfCfg : FuncPtr ge bCfg fdCfg)
    (htyGet : typeOfFundef fdGet = .Tfunction (getSpec c.cpV).tyargs (getSpec c.cpV).tyres
      (getSpec c.cpV).cc)
    (htyCfg : typeOfFundef fdCfg = .Tfunction (cfgSpec c.cfgB c.cfgO).tyargs
      (cfgSpec c.cfgB c.cfgO).tyres (cfgSpec c.cfgB c.cfgO).cc)
    (hGet : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdGet (getSpec c.cpV) vs)
    (hCfg : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdCfg (cfgSpec c.cfgB c.cfgO) vs)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2025_14819_deb_after.f_ossl_cached_x509_store_different)
      (dfSpecA c) vs := by
  rw [fn_after_same]
  exact different_after ge c (hcenv.trans cenv_after_same) hpr hcf hne bGet bCfg fdGet fdCfg hsGet hsCfg
    hfGet hfCfg htyGet htyCfg hGet hCfg vs

/-- **D0（P0）**: 8.14.1 の関数には、部分的な鎖を禁じた設定でもキャッシュを使う入力がある。 -/
theorem P0_C_debian :
    ∃ c : CtxB, (∃ hp m, HB c hp ∧ Heap.Agrees hp m) ∧ permOrder c.pm .Readable = true ∧ IsPtr c.cfV
      ∧ bitOf c.cfgWord 0 = true
      ∧ ∀ (ge : CGenv) (bGet : Block) (fdGet : FunDef),
          ge.genv_cenv = Deb2025_14819_deb_before.prog.prog_comp_env →
          Genv.findSymbol ge.genv_genv Deb2025_14819_deb_before._Curl_ssl_cf_get_primary_config = some bGet →
          FuncPtr ge bGet fdGet →
          typeOfFundef fdGet = .Tfunction (getSpecB (.Vptr c.cpB c.cpO)).tyargs
            (getSpecB (.Vptr c.cpB c.cpO)).tyres (getSpecB (.Vptr c.cpB c.cpO)).cc →
          (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdGet (getSpecB (.Vptr c.cpB c.cpO)) vs) →
          ∀ vs, SatisfiesAt ge (FunctionEntry2 ge)
            (.Internal Deb2025_14819_deb_before.f_ossl_cached_x509_store_different) (dfSpecB c) vs := by
  obtain ⟨c, hsat, hpr, hcf, hbit, h⟩ := P0_C
  refine ⟨c, hsat, hpr, hcf, hbit, fun ge bGet fdGet hcenv hs hf hty hG vs => ?_⟩
  rw [fn_before_same]
  exact h ge bGet fdGet (hcenv.trans cenv_before_same) hs hf hty hG vs

end Deb2025_14819DC

#print axioms Deb2025_14819DC.different_debian
#print axioms Deb2025_14819DC.P0_C_debian
#check @Deb2025_14819DC.different_debian
