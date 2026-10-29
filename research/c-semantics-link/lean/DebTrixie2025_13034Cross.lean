/-
CVE-2025-13034 trixie: P0 を修正後の関数（U1・D1）の上で述べ直す（PROTOCOL-auto §3.10 の確かめ）。

述べ直した文（`P0OnFixedU1`・`P0OnFixedD1`）は、P0（`P0_U0`・`P0_D0`）の関数を修正後のものに置き換え、事後条件 `vpSpecB c false r`
（戻り値は `if verifyhost then r else 0`）を変えないもの。修正後にだけある引数やメモリは無い。

この文は示せなかった。理由は下の `post_conflict_U`・`post_conflict_D`: P0 の前提（`horacle`・`bad`・悪い出来事の式）を満たす値では、
修正後の関数の仕様（`vpSpecA c false r`、P1 の `verify_peer_after` が与える）の戻り値 `r` と、`vpSpecB c false r` の戻り値が違う。
つまり修正後の関数が `vpSpecB` を満たすには、P0 の前提と食い違う `r = 0` が要る。これは述べ直した文の否定の証明ではない
（否定には、仮定を満たす大域環境を作る必要がある）。
-/
import DebTrixie2025_13034U
import DebTrixie2025_13034D
open CC CC.Sep CC.HProp
open Case5C (bitOf)

set_option maxRecDepth 20000

namespace DebTrixie2025_13034X

/-- P0（`P0_U0`）の関数を上流の修正後（U1）に置き換えた文。事後条件 `vpSpecB` は変えない。示せなかった。 -/
def P0OnFixedU1 : Prop :=
    ∃ (c : Case4C.Ctx4) (cfg : H5.Case4.Config) (x : H5.Case4.Cert) (r : Integers.Int),
      (∃ hp m, Case4C.H4 c hp ∧ Heap.Agrees hp m)
      ∧ permOrder c.pm .Readable = true ∧ permOrder c.pm .Nonempty = true ∧ Case4C.Ptrs c
      ∧ cfg.verifyhost = bitOf c.word 0
      ∧ Integers.Int.eq r Integers.Int.zero = H5.Case4.verifyserver cfg x
      ∧ H5.Case4.bad cfg x = true
      ∧ Integers.Int.eq (if bitOf c.word 0 then r else Integers.Int.repr 0) Integers.Int.zero
          = true
      ∧ ∀ (ge : CGenv) (bGet bVs : Block) (fdGet fdVs : FunDef),
          ge.genv_cenv = DebTrixie2025_13034_u1.prog.prog_comp_env →
          Genv.findSymbol ge.genv_genv DebTrixie2025_13034_u1._Curl_ssl_cf_get_primary_config
            = some bGet →
          Genv.findSymbol ge.genv_genv DebTrixie2025_13034_u1._Curl_gtls_verifyserver = some bVs →
          FuncPtr ge bGet fdGet → FuncPtr ge bVs fdVs →
          typeOfFundef fdGet = .Tfunction (Case4C.getSpec (Case4C.cpOf c false)).tyargs
            (Case4C.getSpec (Case4C.cpOf c false)).tyres (Case4C.getSpec (Case4C.cpOf c false)).cc →
          typeOfFundef fdVs = .Tfunction (Case4C.vsSpec r).tyargs (Case4C.vsSpec r).tyres (Case4C.vsSpec r).cc →
          (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdGet (Case4C.getSpec (Case4C.cpOf c false)) vs) →
          (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdVs (Case4C.vsSpec r) vs) →
          ∀ vs, SatisfiesAt ge (FunctionEntry2 ge)
            (.Internal DebTrixie2025_13034_u1.f_Curl_vquic_tls_verify_peer) (Case4C.vpSpecB c false r) vs

/-- P0（`P0_D0`）の関数を Debian の修正後（D1）に置き換えた文。示せなかった。 -/
def P0OnFixedD1 : Prop :=
    ∃ (c : Case4debC.Ctx4) (cfg : H5.Case4.Config) (x : H5.Case4.Cert) (r : Integers.Int),
      (∃ hp m, Case4debC.H4 c hp ∧ Heap.Agrees hp m)
      ∧ permOrder c.pm .Readable = true ∧ permOrder c.pm .Nonempty = true ∧ Case4debC.Ptrs c
      ∧ cfg.verifyhost = bitOf c.word 0
      ∧ Integers.Int.eq r Integers.Int.zero = H5.Case4.verifyserver cfg x
      ∧ H5.Case4.bad cfg x = true
      ∧ Integers.Int.eq (if bitOf c.word 0 then r else Integers.Int.repr 0) Integers.Int.zero
          = true
      ∧ ∀ (ge : CGenv) (bGet bVs : Block) (fdGet fdVs : FunDef),
          ge.genv_cenv = DebTrixie2025_13034_d1.prog.prog_comp_env →
          Genv.findSymbol ge.genv_genv DebTrixie2025_13034_d1._Curl_ssl_cf_get_primary_config
            = some bGet →
          Genv.findSymbol ge.genv_genv DebTrixie2025_13034_d1._Curl_gtls_verifyserver = some bVs →
          FuncPtr ge bGet fdGet → FuncPtr ge bVs fdVs →
          typeOfFundef fdGet = .Tfunction (Case4debC.getSpec (Case4debC.cpOf c false)).tyargs
            (Case4debC.getSpec (Case4debC.cpOf c false)).tyres (Case4debC.getSpec (Case4debC.cpOf c false)).cc →
          typeOfFundef fdVs = .Tfunction (Case4debC.vsSpec r).tyargs (Case4debC.vsSpec r).tyres (Case4debC.vsSpec r).cc →
          (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdGet (Case4debC.getSpec (Case4debC.cpOf c false)) vs) →
          (∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdVs (Case4debC.vsSpec r) vs) →
          ∀ vs, SatisfiesAt ge (FunctionEntry2 ge)
            (.Internal DebTrixie2025_13034_d1.f_Curl_vquic_tls_verify_peer) (Case4debC.vpSpecB c false r) vs

/-- P0 の前提を満たす `r` は、修正後の関数が返す値として、P0 の事後条件の値と一致しない。 -/
theorem post_conflict (word : Integers.Int) (cfg : H5.Case4.Config) (x : H5.Case4.Cert)
    (r : Integers.Int)
    (hor : Integers.Int.eq r Integers.Int.zero = H5.Case4.verifyserver cfg x)
    (hbad : H5.Case4.bad cfg x = true)
    (hev : Integers.Int.eq (if bitOf word 0 then r else Integers.Int.repr 0) Integers.Int.zero
      = true) :
    r ≠ (if bitOf word 0 then r else Integers.Int.repr 0) := by
  have hvs : H5.Case4.verifyserver cfg x = false := H5.Case4.P1 cfg x hbad
  rw [hvs] at hor
  revert hev
  cases bitOf word 0
  · intro _ h
    have h0 : r = Integers.Int.repr 0 := h
    rw [h0] at hor
    exact absurd hor (by decide)
  · intro hev
    have h1 : Integers.Int.eq r Integers.Int.zero = true := hev
    rw [h1] at hor
    exact absurd hor (by decide)

/-- U: P0 の前提では、`vpSpecA c false r`（U1）と `vpSpecB c false r`（U0）の事後条件の戻り値が違う。 -/
theorem post_conflict_U (c : Case4C.Ctx4) (cfg : H5.Case4.Config) (x : H5.Case4.Cert)
    (r : Integers.Int)
    (hor : Integers.Int.eq r Integers.Int.zero = H5.Case4.verifyserver cfg x)
    (hbad : H5.Case4.bad cfg x = true)
    (hev : Integers.Int.eq (if bitOf c.word 0 then r else Integers.Int.repr 0) Integers.Int.zero
      = true) (v : Val) (hp : Heap) :
    (Case4C.vpSpecA c false r).post v hp → ¬ (Case4C.vpSpecB c false r).post v hp := by
  rintro ⟨ha, _⟩ ⟨hb, _⟩
  rw [ha] at hb
  exact post_conflict c.word cfg x r hor hbad hev (Val.Vint.inj hb)

/-- D: 同じことを Case4deb の仕様（D1・D0）で。 -/
theorem post_conflict_D (c : Case4debC.Ctx4) (cfg : H5.Case4.Config) (x : H5.Case4.Cert)
    (r : Integers.Int)
    (hor : Integers.Int.eq r Integers.Int.zero = H5.Case4.verifyserver cfg x)
    (hbad : H5.Case4.bad cfg x = true)
    (hev : Integers.Int.eq (if bitOf c.word 0 then r else Integers.Int.repr 0) Integers.Int.zero
      = true) (v : Val) (hp : Heap) :
    (Case4debC.vpSpecA c false r).post v hp → ¬ (Case4debC.vpSpecB c false r).post v hp := by
  rintro ⟨ha, _⟩ ⟨hb, _⟩
  rw [ha] at hb
  exact post_conflict c.word cfg x r hor hbad hev (Val.Vint.inj hb)

end DebTrixie2025_13034X

#print axioms DebTrixie2025_13034X.post_conflict_U
#print axioms DebTrixie2025_13034X.post_conflict_D
