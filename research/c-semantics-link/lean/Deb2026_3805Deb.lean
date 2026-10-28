/-
CVE-2026-3805: P1・P0 の定理と、Debian のバックポート（D1: curl 8.14.1 に CVE-2026-3805.patch を当てたもの、D0: 8.14.1）への移し替え。

前置きのマクロの展開（`strdup`・`curlx_strdup` → `Curl_cstrdup`、`free`・`curlx_free` → `Curl_cfree`）のあとでは、Debian の翻訳単位から
生成した Clight の関数は、上流の翻訳単位から生成したものと同じ構文木になる（`fn_*_same`、`rfl`）。構造体の環境も同じ（`cenv_*_same`）。
-/
import GenDeb2026_3805DebAfter
import GenDeb2026_3805DebBefore
import Deb2026_3805Before
open CC CC.Sep CC.HProp
open Case4debC (IsPtr)

set_option maxRecDepth 20000

namespace Deb2026_3805DC
open Deb2026_3805C Deb2026_3805B

theorem fn_after_same : Deb2026_3805_deb_after.f_smb_parse_url_path
    = Deb2026_3805_up_after.f_smb_parse_url_path := rfl
theorem cenv_after_same : Deb2026_3805_deb_after.prog.prog_comp_env
    = Deb2026_3805_up_after.prog.prog_comp_env := rfl
theorem fn_before_same : Deb2026_3805_deb_before.f_smb_parse_url_path
    = Deb2026_3805_up_before.f_smb_parse_url_path := rfl
theorem cenv_before_same : Deb2026_3805_deb_before.prog.prog_comp_env
    = Deb2026_3805_up_before.prog.prog_comp_env := rfl

/-- **P1（C）、U1**: 上流の修正後の関数は、CURLE_OK を返したとき、`smbc->share` と `req->path` が別々のブロックの文字列を指す。 -/
theorem P1_C (ge : CGenv) (hcenv : ge.genv_cenv = Deb2026_3805_up_after.prog.prog_comp_env) (c : Ctx)
    (hup : IsPtr c.upV) (hold : IsPtr c.oldV) (X : Ext ge) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_3805_up_after.f_smb_parse_url_path)
      (ppSpecA c) vs)
    ∧ (∀ hp, ppPostA c (.Vint Integers.Int.zero) hp → ∃ bs bq, bs ≠ bq ∧ ∃ fs ns fq nq,
        (cD c ∗ cS c (.Vptr bs Integers.Ptrofs.zero) ∗ arr bs fs (ns + 1)
          ∗ cR c (.Vptr bq Integers.Ptrofs.zero) ∗ strAt bq fq nq) hp) :=
  ⟨parse_after ge hcenv c hup hold X, post_blocks_ne c⟩

/-- **P1（C）、D1**: Debian のバックポートを当てた 8.14.1 の関数でも同じ。 -/
theorem P1_C_debian (ge : CGenv) (hcenv : ge.genv_cenv = Deb2026_3805_deb_after.prog.prog_comp_env) (c : Ctx)
    (hup : IsPtr c.upV) (hold : IsPtr c.oldV) (X : Ext ge) :
    (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_3805_deb_after.f_smb_parse_url_path)
      (ppSpecA c) vs)
    ∧ (∀ hp, ppPostA c (.Vint Integers.Int.zero) hp → ∃ bs bq, bs ≠ bq ∧ ∃ fs ns fq nq,
        (cD c ∗ cS c (.Vptr bs Integers.Ptrofs.zero) ∗ arr bs fs (ns + 1)
          ∗ cR c (.Vptr bq Integers.Ptrofs.zero) ∗ strAt bq fq nq) hp) := by
  rw [fn_after_same]
  exact P1_C ge (hcenv.trans cenv_after_same) c hup hold X

/-- **P0（C）、D0**: 8.14.1 の関数には、`req->path` が `smbc->share` と同じブロックを指したまま CURLE_OK を返す入力がある。 -/
theorem P0_C_debian :
    ∃ (c : Ctx) (x y : PS) (k : Nat) (o : Integers.Ptrofs),
      (∃ hp m, H0 c hp ∧ Heap.Agrees hp m) ∧ IsPtr c.upV ∧ k < y.2.2
      ∧ Integers.Ptrofs.unsigned o = (k : _root_.Int) ∧ Tail y.2.1 0 y.2.2
      ∧ ∀ ge : CGenv, ge.genv_cenv = Deb2026_3805_deb_before.prog.prog_comp_env → ExtB ge x y o →
          ∀ vs, SatisfiesAt ge (FunctionEntry2 ge)
            (.Internal Deb2026_3805_deb_before.f_smb_parse_url_path) (ppSpecB c y k) vs := by
  obtain ⟨c, x, y, k, o, h1, h2, h3, h4, h5, h⟩ := Deb2026_3805B.P0_C
  refine ⟨c, x, y, k, o, h1, h2, h3, h4, h5, fun ge hcenv X vs => ?_⟩
  rw [fn_before_same]
  exact h ge (hcenv.trans cenv_before_same) X vs

end Deb2026_3805DC
