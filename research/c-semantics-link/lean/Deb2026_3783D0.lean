/-
CVE-2026-3783: curl 8.14.1（D0、パッチを当てる前）の `output_auth_headers`。

証明すること（`oah_before`、P0）: `picked == CURLAUTH_BEARER`、`proxy` が偽、`data->set.str[STRING_BEARER]` が NULL でなく、
`Curl_checkheaders` が NULL を返すとき、戻り値は `http_output_bearer(data)` の戻り値 `r`（0 でない任意の値）。
`r` は `http_output_bearer` の仕様だけで決まるので、`http_output_bearer` を呼んでいる。
`Curl_auth_allowed_to_host` が偽を返す仮定（P1 と同じもの）も置くが、修正前の関数は呼ばないので使われない。
-/
import GenDeb2026_3783D0
import Deb2026_3783D1
open CC CC.Sep CC.HProp
open Deb2026_3783_d0
open Case5C (addr call_fwd RR skip_fall)
open Case4debC (lv_field eval_deref_temp return_temp boolVal_int)

set_option maxRecDepth 20000

namespace Deb2026_3783D

theorem cenv_same : Deb2026_3783_d0.prog.prog_comp_env = Deb2026_3783_d1.prog.prog_comp_env := rfl

/-- P0 の仕様: 戻り値は `r`。メモリは変わらない（`done` を書く前に戻る）。 -/
def oahSpecB (c : Ctx) (w r : Integers.Int) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _connectdata noattr),
             tptr (Ty.Tstruct _auth noattr), tptr tschar, tptr tschar, tbool]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = args c false ∧ H c w hp
  post := fun v hp => v = .Vint r ∧ H c w hp
  measure := fun _ => 0

/-- `Curl_checkheaders(data, "Authorization", 13)` は NULL を返す（`Authorization:` を利用者が設定していない）。 -/
def chkSpecNull : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tptr tschar, tulong]
  tyres := tptr tschar
  cc := cc_default
  pre := fun _ hp => emp hp
  post := fun v hp => v = .Vlong (Integers.Int64.repr 0) ∧ emp hp
  measure := fun _ => 0

/-- `http_output_bearer(data)` は `r` を返す。 -/
def bearerSpec (r : Integers.Int) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr)]
  tyres := tint
  cc := cc_default
  pre := fun _ hp => emp hp
  post := fun v hp => v = .Vint r ∧ emp hp
  measure := fun _ => 0

theorem oah_entry_wf0 :
    listNorepet (varNames f_output_auth_headers.fn_vars)
    ∧ listNorepet (varNames f_output_auth_headers.fn_params)
    ∧ listDisjoint (varNames f_output_auth_headers.fn_params)
        (varNames f_output_auth_headers.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem oah_before (ge : CGenv) (c : Ctx) (w r : Integers.Int)
    (hr : Integers.Int.eq r Integers.Int.zero = false) (hbset : c.bset = true)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (bAl bCh bBe bL1 bL4 : Block) (fdAl fdCh fdBe : FunDef)
    (hsAl : Genv.findSymbol ge.genv_genv Deb2026_3783_d1._Curl_auth_allowed_to_host = some bAl)
    (hfAl : FuncPtr ge bAl fdAl)
    (htyAl : typeOfFundef fdAl
      = .Tfunction (allowedSpec false).tyargs (allowedSpec false).tyres (allowedSpec false).cc)
    (hAl : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdAl (allowedSpec false) vs)
    (hsCh : Genv.findSymbol ge.genv_genv _Curl_checkheaders = some bCh)
    (hfCh : FuncPtr ge bCh fdCh)
    (htyCh : typeOfFundef fdCh = .Tfunction chkSpecNull.tyargs chkSpecNull.tyres chkSpecNull.cc)
    (hCh : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdCh chkSpecNull vs)
    (hsBe : Genv.findSymbol ge.genv_genv _http_output_bearer = some bBe)
    (hfBe : FuncPtr ge bBe fdBe)
    (htyBe : typeOfFundef fdBe = .Tfunction (bearerSpec r).tyargs (bearerSpec r).tyres (bearerSpec r).cc)
    (hBe : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdBe (bearerSpec r) vs)
    (hsL1 : Genv.findSymbol ge.genv_genv ___stringlit_1 = some bL1)
    (hsL4 : Genv.findSymbol ge.genv_genv ___stringlit_4 = some bL4)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_output_auth_headers) (oahSpecB c w r) vs := by
  have hcenv1 := hcenv.trans cenv_same
  by_cases hvs : vs = args c false
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := oah_entry_wf0
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) f_output_auth_headers _ _
    (LocalSt emptyEnv [(_proxy, Val.ofBool false), (_path, c.pathV), (_request, c.reqV),
                       (_authstatus, .Vptr c.aB c.aO), (_conn, c.connV),
                       (_data, .Vptr c.dB c.dO)] (H c w))
    (fun m => ?_) ?_
  · refine ⟨PTree.set _proxy (Val.ofBool false) (PTree.set _path c.pathV
              (PTree.set _request c.reqV (PTree.set _authstatus (.Vptr c.aB c.aO)
                (PTree.set _conn c.connV (PTree.set _data (.Vptr c.dB c.dO)
                  (createUndefTemps f_output_auth_headers.fn_temps)))))),
            FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ⟨rfl, ?_, hpre.2⟩⟩
    refine TempsHold_cons ?_ (TempsHold_cons ?_ (TempsHold_cons ?_ (TempsHold_cons ?_
      (TempsHold_cons ?_ (TempsHold_cons ?_ (TempsHold_nil _)))))) <;> ptree_get
  -- auth = NULL; result = CURLE_OK;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ v0
      (fun _ _ _ _ _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ (.Vint (Integers.Int.repr 0))
      (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
  -- Basic の分岐: picked は CURLAUTH_BASIC でない
  refine triple_seq ge _ _ _ ?Qb _ _ _ ?b1 ?b2
  case b1 =>
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ (.Vlong (Integers.Int64.repr 64))
        (fun le m hp hT hH hag => eval_picked hcenv1 hpr
        (hT.get (id := _authstatus) (v := .Vptr c.aB c.aO) (by temps_get)) hH hag)) ?_
    refine triple_if_local ge _ _ emptyEnv _ (H c w) _ false _ _ _
      (fun le m hp hT _ _ =>
        ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
              (EvalExpr.Etempvar _ _ (.Vlong (Integers.Int64.repr 64)) (hT.get (by temps_get)))
              (EvalExpr.Ebinop _ _ _ _ _ _ _
                (EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl) (EvalExpr.Econst_int _ _) rfl)
              rfl, rfl⟩) ?_
    rw [if_neg Bool.false_ne_true]
    exact skip_fall ge _ _ _ _
  case b2 =>
  -- Bearer の分岐から return する（後続は通らない）
  refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?e1 (triple_vacuous ge _ _ _ _)
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ (.Vlong (Integers.Int64.repr 64))
      (fun le m hp hT hH hag => eval_picked hcenv1 hpr
        (hT.get (id := _authstatus) (v := .Vptr c.aB c.aO) (by temps_get)) hH hag)) ?_
  refine triple_if_local ge _ _ emptyEnv _ (H c w) _ true _ _ _
    (fun le m hp hT _ _ =>
      ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ (.Vlong (Integers.Int64.repr 64)) (hT.get (by temps_get)))
            (EvalExpr.Ebinop _ _ _ _ _ _ _
              (EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl) (EvalExpr.Econst_int _ _) rfl)
            rfl, rfl⟩) ?_
  rw [if_pos rfl]
  refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (triple_vacuous ge _ _ _ _)
  -- (!proxy && str[STRING_BEARER]) → t'9 = 1;  t'11 = Curl_checkheaders(...) = NULL → t'10 = 1
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_if_local ge _ _ emptyEnv _ (H c w) _ true _ _ _
        (fun le m hp hT _ _ =>
          ⟨_, EvalExpr.Eunop _ _ _ _ _
            (EvalExpr.Etempvar _ _ (Val.ofBool false) (hT.get (by temps_get))) rfl, rfl⟩)
        (by
          rw [if_pos rfl]
          exact triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ (bearerV c)
              (fun le m hp hT hH hag => eval_bearer hcenv1 hpr
                (hT.get (id := _data) (v := .Vptr c.dB c.dO) (by temps_get)) hH hag))
            (triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ (Val.ofBool true)
              (fun le m hp hT hH hag => EvalExpr.Ecast _ _ _ _
                (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
                (by have := cast_bool_bearer (m := m) (fun _ => bearer_valid hpn hH hag)
                    rwa [hbset] at this)))))
      (triple_if_local ge _ _ emptyEnv _ (H c w) _ true _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool true)
          (hT.get (by temps_get)), rfl⟩)
        (by
          rw [if_pos rfl]
          exact triple_seq_fwd ge _ _ _ _ _ _ _
            (call_fwd ge _ _ chkSpecNull _ _ _ emptyEnv _ emp (H c w) emp (H c w) (H c w)
              _ (.Vlong (Integers.Int64.repr 0)) bCh fdCh hCh hfCh htyCh rfl
              (fun _ _ _ => eval_callee_global rfl hsCh rfl)
              (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
                (EvalExpr.Etempvar _ _ (.Vptr c.dB c.dO) (hT.get (by temps_get))) rfl
                (EvalExprlist.cons _ _ _ _ _ _ _ (eval_callee_global rfl hsL1 rfl) rfl
                  (EvalExprlist.cons _ _ _ _ _ _ _
                    (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Esizeof _ _) (EvalExpr.Econst_int _ _) rfl)
                    rfl EvalExprlist.nil)))
              (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))
            (triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ (Val.ofBool true)
              (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                (EvalExpr.Eunop _ _ _ _ _
                  (EvalExpr.Etempvar _ _ (.Vlong (Integers.Int64.repr 0)) (hT.get (by temps_get))) rfl)
                rfl))))) ?_
  -- if (t'10) { auth = "Bearer"; result = http_output_bearer(data); if (result) return result; }
  refine triple_if_local ge _ _ emptyEnv _ (H c w) _ true _ _ _
    (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool true)
      (hT.get (by temps_get)), rfl⟩) ?_
  rw [if_pos rfl]
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ (.Vptr bL4 Integers.Ptrofs.zero)
      (fun _ _ _ _ _ _ => eval_callee_global rfl hsL4 rfl)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (call_fwd ge _ _ (bearerSpec r) _ _ _ emptyEnv _ emp (H c w) emp (H c w) (H c w)
        [.Vptr c.dB c.dO] (.Vint r) bBe fdBe hBe hfBe htyBe rfl
        (fun _ _ _ => eval_callee_global rfl hsBe rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vptr c.dB c.dO) (hT.get (by temps_get))) rfl EvalExprlist.nil)
        (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))
      (triple_set_local_fwd ge _ _ emptyEnv _ (H c w) _ _ (.Vint r)
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))) ?_
  refine triple_if_local ge _ _ emptyEnv _ (H c w) _ true _ _ _
    (fun le m hp hT _ _ =>
      ⟨_, EvalExpr.Etempvar _ _ (.Vint r) (hT.get (by temps_get)),
        (boolVal_int r m).trans (by rw [hr]; rfl)⟩) ?_
  rw [if_pos rfl]
  exact return_temp ge _ _ _ (H c w) _result r _ _ (by temps_get) rfl (fun hp hH => ⟨rfl, hH⟩)

end Deb2026_3783D
