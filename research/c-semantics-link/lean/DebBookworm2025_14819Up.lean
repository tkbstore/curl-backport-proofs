/-
CVE-2025-14819 bookworm: 上流の修正後（U1、cd046f6c93）・修正前（U0、be3c226bb0）の `ossl_cached_x509_store_different` の上の P1・P0。

上流の2つのコミットは trixie の件（`cases/CVE-2025-14819.md`）と同じである。この件の翻訳単位から生成した Clight の関数と構造体の環境は、
trixie の件の上流の翻訳単位から生成したものと同じ構文木になる（`fn_u1_same` など、`rfl`。違いは epilogue の大域変数の名前だけ）。
そのため trixie の件で証明した `Deb2025_14819C.different_after`・`Deb2025_14819C.different_before` を、等式で書き換えてこの件の関数の上の定理にする。
-/
import GenDebBookworm2025_14819U1
import GenDebBookworm2025_14819U0
import Deb2025_14819After
import Deb2025_14819Before
open CC CC.Sep CC.HProp
open Case5C (bitOf)
open Case4debC (IsPtr)

set_option maxRecDepth 20000

namespace DebBookworm2025_14819C
open Deb2025_14819C

theorem fn_u1_same : DebBookworm2025_14819_u1.f_ossl_cached_x509_store_different
    = Deb2025_14819_up_after.f_ossl_cached_x509_store_different := rfl
theorem cenv_u1_same : DebBookworm2025_14819_u1.prog.prog_comp_env
    = Deb2025_14819_up_after.prog.prog_comp_env := rfl
theorem fn_u0_same : DebBookworm2025_14819_u0.f_ossl_cached_x509_store_different
    = Deb2025_14819_up_before.f_ossl_cached_x509_store_different := rfl
theorem cenv_u0_same : DebBookworm2025_14819_u0.prog.prog_comp_env
    = Deb2025_14819_up_before.prog.prog_comp_env := rfl

/-- **U1（P1）**: 上流の修正後の関数は、記録された `no_partialchain` と今の設定が違えば TRUE を返す。 -/
theorem P1_U1 (ge : CGenv) (c : Ctx)
    (hcenv : ge.genv_cenv = DebBookworm2025_14819_u1.prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hcf : IsPtr c.cfV)
    (hne : bitOf c.mbWord 0 ≠ bitOf c.cfgWord 0)
    (bGet bCfg : Block) (fdGet fdCfg : FunDef)
    (hsGet : Genv.findSymbol ge.genv_genv DebBookworm2025_14819_u1._Curl_ssl_cf_get_primary_config = some bGet)
    (hsCfg : Genv.findSymbol ge.genv_genv DebBookworm2025_14819_u1._Curl_ssl_cf_get_config = some bCfg)
    (hfGet : FuncPtr ge bGet fdGet) (hfCfg : FuncPtr ge bCfg fdCfg)
    (htyGet : typeOfFundef fdGet = .Tfunction (getSpec c.cpV).tyargs (getSpec c.cpV).tyres
      (getSpec c.cpV).cc)
    (htyCfg : typeOfFundef fdCfg = .Tfunction (cfgSpec c.cfgB c.cfgO).tyargs
      (cfgSpec c.cfgB c.cfgO).tyres (cfgSpec c.cfgB c.cfgO).cc)
    (hGet : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdGet (getSpec c.cpV) vs)
    (hCfg : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdCfg (cfgSpec c.cfgB c.cfgO) vs)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal DebBookworm2025_14819_u1.f_ossl_cached_x509_store_different)
      (dfSpecA c) vs := by
  rw [fn_u1_same]
  exact different_after ge c (hcenv.trans cenv_u1_same) hpr hcf hne bGet bCfg fdGet fdCfg hsGet hsCfg
    hfGet hfCfg htyGet htyCfg hGet hCfg vs

/-- **U0（P0）**: 上流の修正前の関数には、部分的な鎖を禁じた設定でもキャッシュを使う入力がある。 -/
theorem P0_U0 :
    ∃ c : CtxB, (∃ hp m, HB c hp ∧ Heap.Agrees hp m) ∧ permOrder c.pm .Readable = true ∧ IsPtr c.cfV
      ∧ bitOf c.cfgWord 0 = true
      ∧ ∀ (ge : CGenv) (bGet : Block) (fdGet : FunDef),
          ge.genv_cenv = DebBookworm2025_14819_u0.prog.prog_comp_env →
          Genv.findSymbol ge.genv_genv DebBookworm2025_14819_u0._Curl_ssl_cf_get_primary_config = some bGet →
          FuncPtr ge bGet fdGet →
          typeOfFundef fdGet = .Tfunction (getSpecB (.Vptr c.cpB c.cpO)).tyargs
            (getSpecB (.Vptr c.cpB c.cpO)).tyres (getSpecB (.Vptr c.cpB c.cpO)).cc →
          (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdGet (getSpecB (.Vptr c.cpB c.cpO)) vs) →
          ∀ vs, SatisfiesAt ge (FunctionEntry2 ge)
            (.Internal DebBookworm2025_14819_u0.f_ossl_cached_x509_store_different) (dfSpecB c) vs := by
  obtain ⟨c, hsat, hpr, hcf, hbit, h⟩ := P0_C
  refine ⟨c, hsat, hpr, hcf, hbit, fun ge bGet fdGet hcenv hs hf hty hG vs => ?_⟩
  rw [fn_u0_same]
  exact h ge bGet fdGet (hcenv.trans cenv_u0_same) hs hf hty hG vs

end DebBookworm2025_14819C

#print axioms DebBookworm2025_14819C.P1_U1
#print axioms DebBookworm2025_14819C.P0_U0
