/-
CVE-2026-4873 D0: curl 8.14.1 に Debian の series の lib/url.c のパッチを CVE-2026-4873 の直前まで当てたもの の `url_match_ssl_use` が `useSpec false false` を満たす。
-/
import Deb2026_4873Tac
open CC CC.Sep CC.HProp
open Case5C (addr flagBit bitOf)

set_option maxRecDepth 20000

namespace Deb2026_4873C

theorem gpf_wf_d0 :
    listNorepet (varNames Deb2026_4873_d0.f_get_protocol_family.fn_vars)
    ∧ listNorepet (varNames Deb2026_4873_d0.f_get_protocol_family.fn_params)
    ∧ listDisjoint (varNames Deb2026_4873_d0.f_get_protocol_family.fn_params)
        (varNames Deb2026_4873_d0.f_get_protocol_family.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem use_wf_d0 :
    listNorepet (varNames Deb2026_4873_d0.f_url_match_ssl_use.fn_vars)
    ∧ listNorepet (varNames Deb2026_4873_d0.f_url_match_ssl_use.fn_params)
    ∧ listDisjoint (varNames Deb2026_4873_d0.f_url_match_ssl_use.fn_params)
        (varNames Deb2026_4873_d0.f_url_match_ssl_use.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- `get_protocol_family` の仕様を本体から示す（仮定ではない）。 -/
theorem gpf_d0 (ge : CGenv) (c : Ctx) (L : Layout ge.genv_cenv "Curl_handler" "handler")
    (hpr : permOrder c.pm .Readable = true) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_4873_d0.f_get_protocol_family)
      (gpfSpec "Curl_handler" c) vs := by
  by_cases hvs : vs = [.Vptr c.cschB c.cschO]
  · subst hvs
    obtain ⟨hnv, hnp, hdisj⟩ := gpf_wf_d0
    refine satisfies_internal_noVars ge (FunctionEntry2 ge) Deb2026_4873_d0.f_get_protocol_family _ _
      (LocalSt emptyEnv [(Deb2026_4873_d0._h, .Vptr c.cschB c.cschO)] (H c)) (fun m => ?_) ?_
    · refine ⟨PTree.set Deb2026_4873_d0._h (.Vptr c.cschB c.cschO)
                (createUndefTemps Deb2026_4873_d0.f_get_protocol_family.fn_temps),
              FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
              fun hp hpre => ?_⟩
      exact ⟨rfl, TempsHold_cons (PTree.gss _ _ _) (TempsHold_nil _), hpre.2⟩
    · refine triple_seq_fwd ge _ _ _ _ _ _ _ (Case5C.triple_nop_loop ge _ _ _) ?_
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (Case5C.triple_nop_loop ge _ _ _) ?_
      refine triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _ _ (.Vlong c.fam)
          (fun le m hp hT hH hag =>
            Case5C.eval_field (hT.get (by temps_mem)) L.co_sch L.off_family rfl
              (H_loads hpr hH hag).fam)) ?_
      exact triple_return_local ge _ _ _ (H c) _ _ (.Vlong c.fam) (.Vlong c.fam)
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
        (fun _ => rfl) (fun hp hH => ⟨rfl, hH⟩)
  · intro k m hp hf _ hpre
    exact absurd hpre.1 hvs

section
/- 合わない候補の単一化で計算に入り込まないように、本体の証明の間だけ次の定義の展開を止める（CVE-2026-1965 と同じ）。 -/
attribute [local irreducible] identOfString Val.ofBool Integers.Int.eq Integers.Int64.eq setLocal dropId

set_option maxHeartbeats 4000000 in
theorem body_d0 (ge : CGenv) (c : Ctx) (ssl : Bool)
    (L : Layout ge.genv_cenv "Curl_handler" "handler")
    (hpr : permOrder c.pm .Readable = true)
    (XS : SslExt ge c ssl) (XG : GpfExt ge "Curl_handler" c) :
    Triple ge (FunctionEntry2 ge) Deb2026_4873_d0.f_url_match_ssl_use
      (LocalSt emptyEnv [(identOfString "m", .Vptr c.mB c.mO),
        (identOfString "conn", .Vptr c.connB c.connO)] (H c))
      Deb2026_4873_d0.f_url_match_ssl_use.fn_body
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no,
        ret := (useSpec false false c ssl).post } := by
  e4go

end

theorem use_d0 (ge : CGenv) (c : Ctx) (ssl : Bool)
    (L : Layout ge.genv_cenv "Curl_handler" "handler")
    (hpr : permOrder c.pm .Readable = true)
    (XS : SslExt ge c ssl) (bG : Block)
    (hsG : Genv.findSymbol ge.genv_genv (identOfString "get_protocol_family") = some bG)
    (hfG : FuncPtr ge bG (.Internal Deb2026_4873_d0.f_get_protocol_family)) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal Deb2026_4873_d0.f_url_match_ssl_use)
      (useSpec false false c ssl) vs := by
  by_cases hvs : vs = [.Vptr c.connB c.connO, .Vptr c.mB c.mO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := use_wf_d0
  have XG : GpfExt ge "Curl_handler" c :=
    ⟨bG, _, hsG, hfG, rfl, gpf_d0 ge c L hpr⟩
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) Deb2026_4873_d0.f_url_match_ssl_use _ _
    (LocalSt emptyEnv [(identOfString "m", .Vptr c.mB c.mO),
      (identOfString "conn", .Vptr c.connB c.connO)] (H c)) (fun m => ?_)
    (body_d0 ge c ssl L hpr XS XG)
  refine ⟨PTree.set (identOfString "m") (.Vptr c.mB c.mO)
            (PTree.set (identOfString "conn") (.Vptr c.connB c.connO)
              (createUndefTemps Deb2026_4873_d0.f_url_match_ssl_use.fn_temps)),
          FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
          fun hp hpre => ?_⟩
  refine ⟨rfl, TempsHold_cons (PTree.gss _ _ _) (TempsHold_cons ?_ (TempsHold_nil _)), hpre.2⟩
  exact (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)

end Deb2026_4873C
