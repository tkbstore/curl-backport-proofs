/-
Case 4（CURL-CVE-2025-13034）: 修正前の `Curl_vquic_tls_verify_peer`（curl 3d91ca8cdb の親 dc34498d18、GnuTLS の構成）。

証明すること（`verify_peer_before`）: 戻り値は
  NULL なら 2、`conn_config->verifyhost` が立っていれば `Curl_gtls_verifyserver` の戻り値 `r`、
  立っていなければ CURLE_OK（`Curl_gtls_verifyserver` は呼ばれない）。
-/
import GenCase4Before
import Case4After
open CC CC.Sep CC.HProp
open Case4_before
open Case5C (addr call_fwd RR return_const skip_end skip_fall boolVal_ofBool_tint eval_bitfield
  bitOf)

set_option maxRecDepth 20000

namespace Case4C

theorem cenv_same4 : prog.prog_comp_env = Case4_after.prog.prog_comp_env := rfl

def vpSpecB (c : Ctx4) (null : Bool) (r : Integers.Int) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _curl_tls_ctx noattr), tptr (Ty.Tstruct _Curl_cfilter noattr),
             tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _ssl_peer noattr)]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp =>
    vargs = [.Vptr c.ctxB c.ctxO, c.cfV, .Vptr c.dataB c.dataO, .Vptr c.peerB c.peerO] ∧ H4 c hp
  post := fun v hp =>
    v = .Vint (if null then Integers.Int.repr 2
               else if bitOf c.word 0 then r else Integers.Int.repr 0) ∧ H4 c hp
  measure := fun _ => 0

theorem vp_entry_wf_b :
    listNorepet (varNames f_Curl_vquic_tls_verify_peer.fn_vars)
    ∧ listNorepet (varNames f_Curl_vquic_tls_verify_peer.fn_params)
    ∧ listDisjoint (varNames f_Curl_vquic_tls_verify_peer.fn_params)
        (varNames f_Curl_vquic_tls_verify_peer.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem boolVal_bit (w : Integers.Int) (m : Mem) :
    Cop.boolVal (.Vint (Cop.bitfieldExtract .I32 .Unsigned 0 1 w)) tint m = some (bitOf w 0) := rfl

/-- 素通りする `skip` で、成り立っている事実 `φ` を後続の前提に持たせる。 -/
theorem skip_fall_fact (ge fe f) (Ret : Val → HProp) (P : Sep.Assn) (φ : Prop) (hφ : φ) :
    Triple ge fe f P .Sskip (RR Ret (fun e le hp => φ ∧ P e le hp)) :=
  triple_conseq ge fe f (triple_skip ge fe f P) (fun _ _ _ x => x) (fun _ _ _ x => ⟨hφ, x⟩)
    (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)

theorem triple_pure_pre (ge fe f) (φ : Prop) (P : Sep.Assn) (s : Stmt) (R : Sep.ExitConds)
    (h : φ → Triple ge fe f P s R) :
    Triple ge fe f (fun e le hp => φ ∧ P e le hp) s R := by
  intro k e le hp hf m hd hag ⟨hφ, hP⟩
  exact h hφ k e le hp hf m hd hag hP

theorem verify_peer_before (ge : CGenv) (c : Ctx4) (null : Bool) (r : Integers.Int)
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
      (vpSpecB c null r) vs := by
  have hcenv' : ge.genv_cenv = Case4_after.prog.prog_comp_env := hcenv.trans cenv_same4
  by_cases hvs : vs = [.Vptr c.ctxB c.ctxO, c.cfV, .Vptr c.dataB c.dataO, .Vptr c.peerB c.peerO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := vp_entry_wf_b
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
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (H4 c) _result _ (.Vint (Integers.Int.repr 0))
      (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (call_fwd ge _ _ (getSpec (cpOf c null)) _t'1 _ _ emptyEnv _ emp (H4 c) emp (H4 c) (H4 c)
        [c.cfV] (cpOf c null) bGet fdGet hGet hfGet htyGet rfl
        (fun _ _ _ => eval_callee_global rfl hsGet rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _cf _ c.cfV (hT.get (by temps_get))) (cast_ptr hptr.cf _ _ m)
          EvalExprlist.nil)
        (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))
      (triple_set_local_fwd ge _ _ emptyEnv _ (H4 c) _conn_config _ (cpOf c null)
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))) ?_
  cases null
  · refine triple_seq ge _ _ _ ?Qn _ _ _ ?i1 ?i2
    case i1 =>
      refine triple_if_local ge _ _ emptyEnv _ (H4 c) _ false _ _ _
        (fun le m hp hT hH hag =>
          ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
                (notbool_validptr (H4_loads hpr hpn hptr hH hag).valid),
           boolVal_ofBool_tint _ m⟩) ?_
      rw [if_neg Bool.false_ne_true]
      exact skip_fall ge _ _ _ _
    case i2 =>
    cases hv : bitOf c.word 0
    · -- verifyhost が立っていない: Curl_gtls_verifyserver を呼ばずに CURLE_OK を返す
      refine triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ emptyEnv _ (H4 c) _t'4 _
            (.Vint (Cop.bitfieldExtract .I32 .Unsigned 0 1 c.word))
            (fun le m hp hT hH hag =>
              eval_bitfield (hT.get (by temps_get)) (hcenv' ▸ co_pc) (hcenv' ▸ off_vh)
                (by decide) (by decide) (H4_loads hpr hpn hptr hH hag).word))
          (triple_if_local ge _ _ emptyEnv _ (H4 c) _ false _ _ _
            (fun le m hp hT _ _ =>
              ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
               (boolVal_bit c.word m).trans (by rw [hv])⟩)
            (by rw [if_neg Bool.false_ne_true]; exact triple_skip ge _ _ _))) ?_
      refine triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_if_local ge _ _ emptyEnv _ (H4 c) _ false _ _ _
          (fun le m hp hT _ _ =>
            ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩)
          (by rw [if_neg Bool.false_ne_true]; exact triple_skip ge _ _ _)) ?_
      exact return_temp ge _ _ _ (H4 c) _result (Integers.Int.repr 0) _ _ (by temps_get) rfl
        (fun hp hH => ⟨by simp [hv], hH⟩)
    · -- verifyhost が立っている: Curl_gtls_verifyserver を呼ぶ
      refine triple_seq ge _ _ _ ?Qv _ _ _ ?v1 ?v2
      case v1 =>
        refine triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ emptyEnv _ (H4 c) _t'4 _
            (.Vint (Cop.bitfieldExtract .I32 .Unsigned 0 1 c.word))
            (fun le m hp hT hH hag =>
              eval_bitfield (hT.get (by temps_get)) (hcenv' ▸ co_pc) (hcenv' ▸ off_vh)
                (by decide) (by decide) (H4_loads hpr hpn hptr hH hag).word)) ?_
        refine triple_if_local ge _ _ emptyEnv _ (H4 c) _ true _ _ _
          (fun le m hp hT _ _ =>
            ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
             (boolVal_bit c.word m).trans (by rw [hv])⟩) ?_
        rw [if_pos rfl]
        refine triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ emptyEnv _ (H4 c) _t'5 _ c.sessV
                (fun le m hp hT hH hag =>
                  eval_session hcenv'
                    (show le.get _ctx = some (.Vptr c.ctxB c.ctxO) from hT.get (by temps_get)) (H4_loads hpr hpn hptr hH hag)))
              (triple_seq_fwd ge _ _ _ _ _ _ _
                (triple_set_local_fwd ge _ _ emptyEnv _ (H4 c) _t'6 _ c.pinV
                  (fun le m hp hT hH hag =>
                    eval_pin hcenv'
                      (show le.get _data = some (.Vptr c.dataB c.dataO) from hT.get (by temps_get)) (H4_loads hpr hpn hptr hH hag)))
                (call_fwd ge _ _ (vsSpec r) _t'2 _ _ emptyEnv _ emp (H4 c) emp (H4 c) (H4 c)
                  _ (.Vint r) bVs fdVs hVs hfVs htyVs rfl
                  (fun _ _ _ => eval_callee_global rfl hsVs rfl)
                  (fun le m hT =>
                    EvalExprlist.cons _ _ _ _ _ _ _
                      (EvalExpr.Etempvar _cf _ c.cfV (hT.get (by temps_get)))
                      (cast_ptr hptr.cf _ _ m)
                      (EvalExprlist.cons _ _ _ _ _ _ _
                        (EvalExpr.Etempvar _data _ (.Vptr c.dataB c.dataO)
                          (hT.get (by temps_get))) rfl
                        (EvalExprlist.cons _ _ _ _ _ _ _
                          (EvalExpr.Etempvar _t'5 _ c.sessV (hT.get (by temps_get)))
                          (cast_ptr hptr.sess _ _ m)
                          (EvalExprlist.cons _ _ _ _ _ _ _
                            (EvalExpr.Etempvar _conn_config _ (.Vptr c.cfgB c.cfgO)
                              (hT.get (by temps_get))) rfl
                            (EvalExprlist.cons _ _ _ _ _ _ _
                              (eval_sslcfg (c := c) hcenv'
                                (show le.get _data = some (.Vptr c.dataB c.dataO) from
                                  hT.get (by temps_get))) rfl
                              (EvalExprlist.cons _ _ _ _ _ _ _
                                (EvalExpr.Etempvar _peer _ (.Vptr c.peerB c.peerO)
                                  (hT.get (by temps_get))) rfl
                                (EvalExprlist.cons _ _ _ _ _ _ _
                                  (EvalExpr.Etempvar _t'6 _ c.pinV (hT.get (by temps_get)))
                                  (cast_ptr hptr.pin _ _ m) EvalExprlist.nil)))))))
                  (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))))
            (triple_set_local_fwd ge _ _ emptyEnv _ (H4 c) _result _ (.Vint r)
              (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))) ?_
        cases hr : Integers.Int.eq r Integers.Int.zero
        · refine triple_if_local ge _ _ emptyEnv _ (H4 c) _ true _ _ _
            (fun le m hp hT _ _ =>
              ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
               (boolVal_int r m).trans (by rw [hr]; rfl)⟩) ?_
          rw [if_pos rfl]
          exact return_temp ge _ _ _ (H4 c) _result r _ _ (by temps_get) rfl
            (fun hp hH => ⟨by simp [hv], hH⟩)
        · refine triple_if_local ge _ _ emptyEnv _ (H4 c) _ false _ _ _
            (fun le m hp hT _ _ =>
              ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
               (boolVal_int r m).trans (by rw [hr]; rfl)⟩) ?_
          rw [if_neg Bool.false_ne_true]
          exact skip_fall_fact ge _ _ _ _ (Integers.Int.eq r Integers.Int.zero = true) hr
      case v2 =>
        -- 前の文を素通りしたのは r = CURLE_OK のときだけ
        refine triple_pure_pre ge _ _ _ _ _ _ (fun hr => ?_)
        refine triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_if_local ge _ _ emptyEnv _ (H4 c) _ false _ _ _
            (fun le m hp hT _ _ =>
              ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
               (boolVal_int r m).trans (by rw [hr]; rfl)⟩)
            (by rw [if_neg Bool.false_ne_true]; exact triple_skip ge _ _ _)) ?_
        exact return_temp ge _ _ _ (H4 c) _result r _ _ (by temps_get) rfl
          (fun hp hH => ⟨by simp [hv], hH⟩)
  · refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (triple_vacuous ge _ _ _ _)
    refine triple_if_local ge _ _ emptyEnv _ (H4 c) _ true _ _ _
      (fun le m hp hT _ _ =>
        ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
              notbool_null,
         boolVal_ofBool_tint _ m⟩) ?_
    rw [if_pos rfl]
    exact return_const ge _ _ _ _ _ _ _ (.Vint (Integers.Int.repr 2)) (fun _ => rfl)
      (fun hp hH => ⟨rfl, hH⟩)

end Case4C
