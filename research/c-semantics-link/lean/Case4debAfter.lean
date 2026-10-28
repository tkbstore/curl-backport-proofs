/-
Case 4 の Debian バックポート（CVE-2025-13034）: 修正後の `Curl_vquic_tls_verify_peer`（curl 8.14.1 に Debian の CVE-2025-13034.patch を当てたもの、GnuTLS の構成）。Case4After.lean との違いは、`Curl_gtls_verifyserver` に `cf` を渡さないことだけ。

証明すること（`verify_peer_after`）: 戻り値は
  `Curl_ssl_cf_get_primary_config` が NULL なら CURLE_FAILED_INIT（2）、そうでなければ `Curl_gtls_verifyserver` の戻り値 `r`。
-/
import Case4debCommon
import Case5After
open CC CC.Sep CC.HProp
open Case4deb_after
open Case5C (addr call_fwd RR return_const skip_end skip_fall boolVal_ofBool_tint)

set_option maxRecDepth 20000

namespace Case4debC

/-- `conn_config` の値: NULL（`Vlong 0`）か、所有しているセルを指すポインタ。 -/
def cpOf (c : Ctx4) (null : Bool) : Val :=
  if null then .Vlong Integers.Int64.zero else .Vptr c.cfgB c.cfgO

def vpSpecA (c : Ctx4) (null : Bool) (r : Integers.Int) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _curl_tls_ctx noattr), tptr (Ty.Tstruct _Curl_cfilter noattr),
             tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _ssl_peer noattr)]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp =>
    vargs = [.Vptr c.ctxB c.ctxO, c.cfV, .Vptr c.dataB c.dataO, .Vptr c.peerB c.peerO] ∧ H4 c hp
  post := fun v hp => v = .Vint (if null then Integers.Int.repr 2 else r) ∧ H4 c hp
  measure := fun _ => 0

theorem vp_entry_wf :
    listNorepet (varNames f_Curl_vquic_tls_verify_peer.fn_vars)
    ∧ listNorepet (varNames f_Curl_vquic_tls_verify_peer.fn_params)
    ∧ listDisjoint (varNames f_Curl_vquic_tls_verify_peer.fn_params)
        (varNames f_Curl_vquic_tls_verify_peer.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem notbool_validptr {b : Block} {o : Integers.Ptrofs} {m : Mem}
    (hv : Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) :
    Cop.semUnaryOperation .Onotbool (.Vptr b o) (tptr (Ty.Tstruct _ssl_primary_config noattr)) m
      = some (Val.ofBool false) := by
  simp only [Cop.semUnaryOperation, Cop.semNotbool, Cop.boolVal, hv]
  rfl

theorem notbool_null {m : Mem} :
    Cop.semUnaryOperation .Onotbool (.Vlong Integers.Int64.zero)
      (tptr (Ty.Tstruct _ssl_primary_config noattr)) m
      = some (Val.ofBool true) := rfl

theorem boolVal_int (r : Integers.Int) (m : Mem) :
    Cop.boolVal (.Vint r) tint m = some (!Integers.Int.eq r Integers.Int.zero) := rfl

/-- `return t;`（`t` は `int` の一時変数）。 -/
theorem return_temp (ge fe f) (l : List (Ident × Val)) (Hh : HProp) (t : Ident) (r : Integers.Int)
    (Ret : Val → HProp) (Q : Sep.Assn)
    (hmem : (t, Val.Vint r) ∈ l)
    (hret : f.fn_return = tint)
    (hpost : ∀ hp, Hh hp → Ret (.Vint r) hp) :
    Triple ge fe f (LocalSt emptyEnv l Hh) (.Sreturn (some (.Etempvar t tint))) (RR Ret Q) :=
  triple_conseq ge fe f
    (triple_return_local ge fe f l Hh _ Ret (.Vint r) (.Vint r)
      (fun _ _ _ hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get hmem)) (fun _ => by rw [hret]; rfl)
      hpost)
    (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun _ _ _ x => x) (fun _ _ _ x => x)
    (fun _ _ x => x)

theorem verify_peer_after (ge : CGenv) (c : Ctx4) (null : Bool) (r : Integers.Int)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hptr : Ptrs c)
    (bGet bVs : Block) (fdGet fdVs : FunDef)
    (hsGet : Genv.findSymbol ge.genv_genv _Curl_ssl_cf_get_primary_config = some bGet)
    (hsVs : Genv.findSymbol ge.genv_genv _Curl_gtls_verifyserver = some bVs)
    (hfGet : FuncPtr ge bGet fdGet) (hfVs : FuncPtr ge bVs fdVs)
    (htyGet : typeOfFundef fdGet
      = .Tfunction (getSpec (cpOf c null)).tyargs (getSpec (cpOf c null)).tyres
          (getSpec (cpOf c null)).cc)
    (htyVs : typeOfFundef fdVs = .Tfunction (vsSpec r).tyargs (vsSpec r).tyres (vsSpec r).cc)
    (hGet : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdGet (getSpec (cpOf c null)) vs)
    (hVs : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdVs (vsSpec r) vs)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_Curl_vquic_tls_verify_peer)
      (vpSpecA c null r) vs := by
  by_cases hvs : vs = [.Vptr c.ctxB c.ctxO, c.cfV, .Vptr c.dataB c.dataO, .Vptr c.peerB c.peerO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := vp_entry_wf
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) f_Curl_vquic_tls_verify_peer _ _
    (LocalSt emptyEnv [(_peer, .Vptr c.peerB c.peerO), (_data, .Vptr c.dataB c.dataO),
                       (_cf, c.cfV), (_ctx, .Vptr c.ctxB c.ctxO)] (H4 c))
    (fun m => ?_) ?_
  · refine ⟨PTree.set _peer (.Vptr c.peerB c.peerO)
              (PTree.set _data (.Vptr c.dataB c.dataO)
                (PTree.set _cf c.cfV
                  (PTree.set _ctx (.Vptr c.ctxB c.ctxO)
                    (createUndefTemps f_Curl_vquic_tls_verify_peer.fn_temps)))),
            FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    refine ⟨rfl, TempsHold_cons (PTree.gss _ _ _) (TempsHold_cons ?_ (TempsHold_cons ?_
      (TempsHold_cons ?_ (TempsHold_nil _)))), hpre.2⟩
    · exact (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)
    · exact (PTree.gso _ _ _ _ (by decide)).trans ((PTree.gso _ _ _ _ (by decide)).trans
        (PTree.gss _ _ _))
    · exact (PTree.gso _ _ _ _ (by decide)).trans ((PTree.gso _ _ _ _ (by decide)).trans
        ((PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)))
  -- result = CURLE_OK;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (H4 c) _result _ (.Vint (Integers.Int.repr 0))
      (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
  -- conn_config = Curl_ssl_cf_get_primary_config(cf);
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (call_fwd ge _ _ (getSpec (cpOf c null)) _t'1 _ _ emptyEnv _ emp (H4 c) emp (H4 c) (H4 c)
        [c.cfV] (cpOf c null) bGet fdGet hGet hfGet htyGet rfl
        (fun _ _ _ => eval_callee_global rfl hsGet rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ c.cfV (hT.get (by temps_get))) (cast_ptr hptr.cf _ _ m)
          EvalExprlist.nil)
        (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))
      (triple_set_local_fwd ge _ _ emptyEnv _ (H4 c) _conn_config _ (cpOf c null)
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))) ?_
  cases null
  · -- conn_config は NULL でない
    refine triple_seq ge _ _ _ ?Qn _ _ _ ?i1 ?i2
    case i1 =>
      refine triple_if_local ge _ _ emptyEnv _ (H4 c) _ false _ _ _
        (fun le m hp hT hH hag =>
          ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
                (notbool_validptr (H4_loads hpr hpn hptr hH hag).valid),
           boolVal_ofBool_tint _ m⟩) ?_
      rw [if_neg Bool.false_ne_true]
      exact skip_fall ge _ _ _ _
    case i2 =>
    -- t'4 = ctx->gtls.session; t'5 = data->set.str[...]; t'2 = Curl_gtls_verifyserver(...); result = t'2;
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ emptyEnv _ (H4 c) _t'4 _ c.sessV
            (fun le m hp hT hH hag =>
              eval_session hcenv (hT.get (by temps_get)) (H4_loads hpr hpn hptr hH hag)))
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ (H4 c) _t'5 _ c.pinV
              (fun le m hp hT hH hag =>
                eval_pin hcenv (hT.get (by temps_get)) (H4_loads hpr hpn hptr hH hag)))
            (call_fwd ge _ _ (vsSpec r) _t'2 _ _ emptyEnv _ emp (H4 c) emp (H4 c) (H4 c)
              _ (.Vint r) bVs fdVs hVs hfVs htyVs rfl
              (fun _ _ _ => eval_callee_global rfl hsVs rfl)
              (fun le m hT =>
                EvalExprlist.cons _ _ _ _ _ _ _
                    (EvalExpr.Etempvar _data _ (.Vptr c.dataB c.dataO) (hT.get (by temps_get))) rfl
                    (EvalExprlist.cons _ _ _ _ _ _ _
                      (EvalExpr.Etempvar _t'4 _ c.sessV (hT.get (by temps_get)))
                      (cast_ptr hptr.sess _ _ m)
                      (EvalExprlist.cons _ _ _ _ _ _ _
                        (EvalExpr.Etempvar _conn_config _ (.Vptr c.cfgB c.cfgO)
                          (hT.get (by temps_get))) rfl
                        (EvalExprlist.cons _ _ _ _ _ _ _
                          (eval_sslcfg (c := c) hcenv (hT.get (by temps_get))) rfl
                          (EvalExprlist.cons _ _ _ _ _ _ _
                            (EvalExpr.Etempvar _peer _ (.Vptr c.peerB c.peerO)
                              (hT.get (by temps_get))) rfl
                            (EvalExprlist.cons _ _ _ _ _ _ _
                              (EvalExpr.Etempvar _t'5 _ c.pinV (hT.get (by temps_get)))
                              (cast_ptr hptr.pin _ _ m) EvalExprlist.nil))))))
              (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))))
        (triple_set_local_fwd ge _ _ emptyEnv _ (H4 c) _result _ (.Vint r)
          (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))) ?_
    cases hr : Integers.Int.eq r Integers.Int.zero
    · -- r ≠ CURLE_OK: if (result) return result;
      refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (triple_vacuous ge _ _ _ _)
      refine triple_if_local ge _ _ emptyEnv _ (H4 c) _ true _ _ _
        (fun le m hp hT _ _ =>
          ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), (boolVal_int r m).trans (by rw [hr]; rfl)⟩) ?_
      rw [if_pos rfl]
      exact return_temp ge _ _ _ (H4 c) _result r _ _ (by temps_get) rfl
        (fun hp hH => ⟨rfl, hH⟩)
    · -- r = CURLE_OK: 2つの if を素通りして return result;
      refine triple_seq ge _ _ _ ?Qa _ _ _ ?j1 ?j2
      case j1 =>
        refine triple_if_local ge _ _ emptyEnv _ (H4 c) _ false _ _ _
          (fun le m hp hT _ _ =>
            ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), (boolVal_int r m).trans (by rw [hr]; rfl)⟩) ?_
        rw [if_neg Bool.false_ne_true]
        exact skip_fall ge _ _ _ _
      case j2 =>
        refine triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_if_local ge _ _ emptyEnv _ (H4 c) _ false _ _ _
            (fun le m hp hT _ _ =>
              ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), (boolVal_int r m).trans (by rw [hr]; rfl)⟩)
            (by rw [if_neg Bool.false_ne_true]; exact triple_skip ge _ _ _)) ?_
        exact return_temp ge _ _ _ (H4 c) _result r _ _ (by temps_get) rfl
          (fun hp hH => ⟨rfl, hH⟩)
  · -- conn_config は NULL: return CURLE_FAILED_INIT;
    refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (triple_vacuous ge _ _ _ _)
    refine triple_if_local ge _ _ emptyEnv _ (H4 c) _ true _ _ _
      (fun le m hp hT _ _ =>
        ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
              notbool_null,
         boolVal_ofBool_tint _ m⟩) ?_
    rw [if_pos rfl]
    exact return_const ge _ _ _ _ _ _ _ (.Vint (Integers.Int.repr 2)) (fun _ => rfl)
      (fun hp hH => ⟨rfl, hH⟩)

end Case4debC
