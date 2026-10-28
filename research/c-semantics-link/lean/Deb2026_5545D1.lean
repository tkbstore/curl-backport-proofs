/-
CVE-2026-5545 D1: curl 8.14.1 に Debian の series の lib/url.c のパッチを CVE-2026-5545 まで当てたもの の `url_match_auth_ntlm` が `ntlmSpec true` を満たす。
-/
import Deb2026_5545Tac
open CC CC.Sep CC.HProp
open Case5C (addr bitOf)
open Case4C (IsPtr)

set_option maxRecDepth 20000

namespace Deb2026_5545C

theorem entry_wf_d1 :
    listNorepet (varNames Deb2026_5545_d1.f_url_match_auth_ntlm.fn_vars)
    ∧ listNorepet (varNames Deb2026_5545_d1.f_url_match_auth_ntlm.fn_params)
    ∧ listDisjoint (varNames Deb2026_5545_d1.f_url_match_auth_ntlm.fn_params)
        (varNames Deb2026_5545_d1.f_url_match_auth_ntlm.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

section
/- 合わない候補の単一化で計算に入り込まないように、本体の証明の間だけ次の定義の展開を止める:
   `identOfString`（識別子）、`forceWord`、`Val.ofBool`、`Integers.Int.eq`、`setLocal`・`dropId`（一時変数の表）。
   識別子が等しくないことは `with_unfolding_all decide` で示す（`tget`）。証明の中身は変わらない。 -/
attribute [local irreducible] identOfString forceWord Val.ofBool Integers.Int.eq setLocal dropId

set_option maxHeartbeats 4000000 in
theorem body_d1 (ge : CGenv) (c : Ctx) (fv : Val) (w : Integers.Int)
    (cmp : Val → Val → Integers.Int) (L : Layout ge.genv_cenv)
    (hpr : permOrder c.pm .Readable = true) (hpw : permOrder c.pm .Writable = true)
    (hptr : Ptrs c) (X : Deb2026_1965C.TsExt ge cmp) :
    Triple ge (FunctionEntry2 ge) Deb2026_5545_d1.f_url_match_auth_ntlm
      (LocalSt emptyEnv [(identOfString "m", .Vptr c.mB c.mO),
        (identOfString "conn", .Vptr c.connB c.connO)] (H c fv w))
      Deb2026_5545_d1.f_url_match_auth_ntlm.fn_body
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := (ntlmSpec true c fv w cmp).post } := by
  have p1 := hptr.nu
  have p2 := hptr.np
  have p3 := hptr.cu
  have p4 := hptr.cp
  n5go

end

theorem ntlm_d1 (ge : CGenv) (c : Ctx) (fv : Val) (w : Integers.Int)
    (cmp : Val → Val → Integers.Int) (L : Layout ge.genv_cenv)
    (hpr : permOrder c.pm .Readable = true) (hpw : permOrder c.pm .Writable = true)
    (hptr : Ptrs c) (X : Deb2026_1965C.TsExt ge cmp) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_5545_d1.f_url_match_auth_ntlm)
      (ntlmSpec true c fv w cmp) vs := by
  by_cases hvs : vs = [.Vptr c.connB c.connO, .Vptr c.mB c.mO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := entry_wf_d1
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) Deb2026_5545_d1.f_url_match_auth_ntlm _ _
    (LocalSt emptyEnv [(identOfString "m", .Vptr c.mB c.mO),
      (identOfString "conn", .Vptr c.connB c.connO)] (H c fv w)) (fun m => ?_)
    (body_d1 ge c fv w cmp L hpr hpw hptr X)
  refine ⟨PTree.set (identOfString "m") (.Vptr c.mB c.mO)
            (PTree.set (identOfString "conn") (.Vptr c.connB c.connO)
              (createUndefTemps Deb2026_5545_d1.f_url_match_auth_ntlm.fn_temps)),
          FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
          fun hp hpre => ?_⟩
  refine ⟨rfl, TempsHold_cons (PTree.gss _ _ _) (TempsHold_cons ?_ (TempsHold_nil _)), hpre.2⟩
  exact (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)

end Deb2026_5545C
