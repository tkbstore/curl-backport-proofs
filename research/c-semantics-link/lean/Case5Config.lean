/-
Case 5（CURL-CVE-2026-86411）: `url_match_ssl_config`（修正の前後で同じ）。

証明すること: C の関数は、H5 のモデルの `sslConfig` と同じ値を返す（`ssl_config_eq`）。
-/
import Case5Common
open CC CC.Sep CC.HProp
open Case5_after

set_option maxRecDepth 20000

namespace Case5C

/-- `url_match_ssl_config` の仕様: 戻り値は H5 の `sslConfig`、メモリは変えない。
    `sslConfig` は `connSSL` を見ないので、`ssl` は何でもよい。 -/
def configSpec (c : Ctx) (ssl cfg : Bool) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _connectdata noattr), tptr (Ty.Tstruct _url_conn_match noattr)]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.connB c.connO, .Vptr c.mB c.mO] ∧ H c hp
  post := fun v hp => v = Val.ofBool (H5.Case5.sslConfig (input c ssl cfg)) ∧ H c hp
  measure := fun _ => 0

theorem config_entry_wf :
    listNorepet (varNames f_url_match_ssl_config.fn_vars)
    ∧ listNorepet (varNames f_url_match_ssl_config.fn_params)
    ∧ listDisjoint (varNames f_url_match_ssl_config.fn_params)
        (varNames f_url_match_ssl_config.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem cast_int_bool (n : Integers.Int) (m : Mem) :
    Cop.semCast (.Vint n) tint tbool m = some (Val.ofBool (!Integers.Int.eq n Integers.Int.zero)) := by
  unfold Cop.semCast
  cases h : Integers.Int.eq n Integers.Int.zero <;> simp [h] <;> rfl

theorem cast_ofBool_bool (b : Bool) (m : Mem) :
    Cop.semCast (Val.ofBool b) tint tbool m = some (Val.ofBool b) := by
  cases b <;> rfl

theorem ssl_config_eq (ge : CGenv) (c : Ctx) (ssl cfg : Bool)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true)
    (bCfg : Block) (fdCfg : FunDef)
    (hsCfg : Genv.findSymbol ge.genv_genv _Curl_ssl_conn_config_match = some bCfg)
    (hfCfg : FuncPtr ge bCfg fdCfg)
    (htyCfg : typeOfFundef fdCfg
      = .Tfunction (cfgSpec c cfg).tyargs (cfgSpec c cfg).tyres (cfgSpec c cfg).cc)
    (hCfg : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdCfg (cfgSpec c cfg) vs)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_url_match_ssl_config)
      (configSpec c ssl cfg) vs := by
  by_cases hvs : vs = [.Vptr c.connB c.connO, .Vptr c.mB c.mO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := config_entry_wf
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) f_url_match_ssl_config _ _
    (LocalSt emptyEnv [(_m, .Vptr c.mB c.mO), (_conn, .Vptr c.connB c.connO)] (H c))
    (fun m => ?_) ?_
  · refine ⟨PTree.set _m (.Vptr c.mB c.mO)
              (PTree.set _conn (.Vptr c.connB c.connO)
                (createUndefTemps f_url_match_ssl_config.fn_temps)),
            FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    refine ⟨rfl, TempsHold_cons (PTree.gss _ _ _) (TempsHold_cons ?_ (TempsHold_nil _)), hpre.2⟩
    exact (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)
  refine triple_seq ge _ _ _
    (fun e _ hp => e = emptyEnv ∧ H5.Case5.sslConfig (input c ssl cfg) = true ∧ H c hp)
    _ _ _ ?body ?ret1
  case ret1 =>
    refine triple_pre ge _ _
      (P := LocalSt emptyEnv [] (fun hp => H5.Case5.sslConfig (input c ssl cfg) = true ∧ H c hp))
      (fun e le hp ⟨he, hφ, hH⟩ => ⟨he, TempsHold_nil _, hφ, hH⟩) ?_
    exact triple_return_local ge _ _ [] _ _ _ (.Vint (Integers.Int.repr 1)) (Val.ofBool true)
      (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _) (fun _ => rfl)
      (fun hp ⟨hφ, hH⟩ => ⟨by rw [hφ], hH⟩)
  case body =>
  -- { t'1 = (needle が SSL) || may_tls; t'2 = t'1 ? !Curl_ssl_conn_config_match(…) : 0 }
  -- if (t'2) { DEBUGF; return 0; }
  cases hn : flagBit c.flags 0
  · -- needle は SSL でない: t'1 = (_Bool) m->may_tls
    cases hmt : bitOf c.bits 0
    · -- may_tls も 0: t'2 = 0 なので戻らない
      refine triple_seq_fwd ge _ _ _ ?Qa _ _ _ ?a1 ?a2
      case a1 =>
        refine triple_seq_fwd ge _ _ _ ?Qa' _ _ _ ?a11 ?a12
        case a11 =>
          refine triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'5 _ (.Vptr c.ndlB c.ndlO)
              (fun le m hp hT hH hag =>
                eval_field (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_needle) rfl
                  (H_loads hpr hH hag).needle)) ?_
          refine triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'6 _ (.Vptr c.nschB c.nschO)
              (fun le m hp hT hH hag =>
                eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_scheme) rfl
                  (H_loads hpr hH hag).nsch)) ?_
          refine triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'7 _ (.Vint c.flags)
              (fun le m hp hT hH hag =>
                eval_field (hT.get (by temps_get)) (hcenv ▸ co_scheme) (hcenv ▸ off_flags) rfl
                  (H_loads hpr hH hag).flags)) ?_
          refine triple_if_local ge _ _ emptyEnv _ (H c) _ false _ _ _
            (fun le m hp hT _ _ =>
              ⟨_, eval_flag0 (hT.get (by temps_get)), hn ▸ boolVal_flag0 c.flags m⟩) ?_
          rw [if_neg Bool.false_ne_true]
          refine triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'8 _
              (.Vint (Cop.bitfieldExtract .I32 .Unsigned 0 1 c.bits))
              (fun le m hp hT hH hag =>
                eval_bitfield (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_may_tls)
                  (by decide) (by decide) (H_loads hpr hH hag).bits)) ?_
          refine triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'1 _ (Val.ofBool (bitOf c.bits 0)) ?_
          intro le m hp hT _ _
          exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
            (cast_int_bool _ m)
        case a12 =>
          refine triple_if_local ge _ _ emptyEnv _ (H c) _ false _ _ _
            (fun le m hp hT _ _ =>
              ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
               by rw [hmt]; exact boolVal_ofBool_tint _ m⟩) ?_
          rw [if_neg Bool.false_ne_true]
          exact triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'2 _ (.Vint (Integers.Int.repr 0))
            (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)
      case a2 =>
        refine triple_if_local ge _ _ emptyEnv _ (H c) _ false _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩) ?_
        rw [if_neg Bool.false_ne_true]
        exact skip_end ge _ _ _ _ _ _ (by simp [H5.Case5.sslConfig, input, hn, hmt])
    · -- may_tls が 1: 設定の一致を確かめる
      refine triple_seq_fwd ge _ _ _ ?Qb _ _ _ ?b1 ?b2
      case b1 =>
        refine triple_seq_fwd ge _ _ _ ?Qb' _ _ _ ?b11 ?b12
        case b11 =>
          refine triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'5 _ (.Vptr c.ndlB c.ndlO)
              (fun le m hp hT hH hag =>
                eval_field (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_needle) rfl
                  (H_loads hpr hH hag).needle)) ?_
          refine triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'6 _ (.Vptr c.nschB c.nschO)
              (fun le m hp hT hH hag =>
                eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_scheme) rfl
                  (H_loads hpr hH hag).nsch)) ?_
          refine triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'7 _ (.Vint c.flags)
              (fun le m hp hT hH hag =>
                eval_field (hT.get (by temps_get)) (hcenv ▸ co_scheme) (hcenv ▸ off_flags) rfl
                  (H_loads hpr hH hag).flags)) ?_
          refine triple_if_local ge _ _ emptyEnv _ (H c) _ false _ _ _
            (fun le m hp hT _ _ =>
              ⟨_, eval_flag0 (hT.get (by temps_get)), hn ▸ boolVal_flag0 c.flags m⟩) ?_
          rw [if_neg Bool.false_ne_true]
          refine triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'8 _
              (.Vint (Cop.bitfieldExtract .I32 .Unsigned 0 1 c.bits))
              (fun le m hp hT hH hag =>
                eval_bitfield (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_may_tls)
                  (by decide) (by decide) (H_loads hpr hH hag).bits)) ?_
          refine triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'1 _ (Val.ofBool (bitOf c.bits 0)) ?_
          intro le m hp hT _ _
          exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
            (cast_int_bool _ m)
        case b12 =>
          refine triple_if_local ge _ _ emptyEnv _ (H c) _ true _ _ _
            (fun le m hp hT _ _ =>
              ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
               by rw [hmt]; exact boolVal_ofBool_tint _ m⟩) ?_
          rw [if_pos rfl]
          refine triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'4 _ (.Vptr c.dataB c.dataO)
                (fun le m hp hT hH hag =>
                  eval_field (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_data) rfl
                    (H_loads hpr hH hag).data))
              (call_fwd ge _ _ (cfgSpec c cfg) _t'3 _ _ emptyEnv _ emp (H c) emp (H c) (H c)
                [.Vptr c.dataB c.dataO, .Vptr c.connB c.connO, .Vint (Integers.Int.repr 0)]
                (Val.ofBool cfg) bCfg fdCfg hCfg hfCfg htyCfg rfl
                (fun _ _ _ => eval_callee_global rfl hsCfg rfl)
                (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
                  (EvalExpr.Etempvar _ _ (.Vptr c.dataB c.dataO) (hT.get (by temps_get))) rfl
                  (EvalExprlist.cons _ _ _ _ _ _ _
                    (EvalExpr.Etempvar _ _ (.Vptr c.connB c.connO) (hT.get (by temps_get))) rfl
                    (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl EvalExprlist.nil)))
                (fun _ he => ⟨rfl, he⟩) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))) ?_
          refine triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'2 _ (Val.ofBool (!cfg)) ?_
          intro le m hp hT _ _
          exact EvalExpr.Ecast _ _ _ _
            (EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (notbool_ofBool cfg m))
            (cast_ofBool_bool _ m)
      case b2 =>
        refine triple_if_local ge _ _ emptyEnv _ (H c) _ (!cfg) _ _ _
          (fun le m hp hT _ _ =>
            ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), boolVal_ofBool_tint _ m⟩) ?_
        cases cfg
        · rw [if_pos (show (!false) = true from rfl)]
          refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_nop_loop ge _ _ _) ?_
          exact return_const ge _ _ _ _ _ _ _ (Val.ofBool false) (fun _ => rfl)
            (fun hp hH => ⟨by simp [H5.Case5.sslConfig, input, hn, hmt], hH⟩)
        · rw [if_neg (show ¬((!true) = true) from by decide)]
          exact skip_end ge _ _ _ _ _ _ (by simp [H5.Case5.sslConfig, input, hn, hmt])
  · -- needle は SSL: t'1 = 1、設定の一致を確かめる
    refine triple_seq_fwd ge _ _ _ ?Qc _ _ _ ?c1 ?c2
    case c1 =>
      refine triple_seq_fwd ge _ _ _ ?Qc' _ _ _ ?c11 ?c12
      case c11 =>
        refine triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'5 _ (.Vptr c.ndlB c.ndlO)
            (fun le m hp hT hH hag =>
              eval_field (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_needle) rfl
                (H_loads hpr hH hag).needle)) ?_
        refine triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'6 _ (.Vptr c.nschB c.nschO)
            (fun le m hp hT hH hag =>
              eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_scheme) rfl
                (H_loads hpr hH hag).nsch)) ?_
        refine triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'7 _ (.Vint c.flags)
            (fun le m hp hT hH hag =>
              eval_field (hT.get (by temps_get)) (hcenv ▸ co_scheme) (hcenv ▸ off_flags) rfl
                (H_loads hpr hH hag).flags)) ?_
        refine triple_if_local ge _ _ emptyEnv _ (H c) _ true _ _ _
          (fun le m hp hT _ _ =>
            ⟨_, eval_flag0 (hT.get (by temps_get)), hn ▸ boolVal_flag0 c.flags m⟩) ?_
        rw [if_pos rfl]
        exact triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'1 _ (.Vint (Integers.Int.repr 1))
          (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)
      case c12 =>
        refine triple_if_local ge _ _ emptyEnv _ (H c) _ true _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩) ?_
        rw [if_pos rfl]
        refine triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'4 _ (.Vptr c.dataB c.dataO)
              (fun le m hp hT hH hag =>
                eval_field (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_data) rfl
                  (H_loads hpr hH hag).data))
            (call_fwd ge _ _ (cfgSpec c cfg) _t'3 _ _ emptyEnv _ emp (H c) emp (H c) (H c)
              [.Vptr c.dataB c.dataO, .Vptr c.connB c.connO, .Vint (Integers.Int.repr 0)]
              (Val.ofBool cfg) bCfg fdCfg hCfg hfCfg htyCfg rfl
              (fun _ _ _ => eval_callee_global rfl hsCfg rfl)
              (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
                (EvalExpr.Etempvar _ _ (.Vptr c.dataB c.dataO) (hT.get (by temps_get))) rfl
                (EvalExprlist.cons _ _ _ _ _ _ _
                  (EvalExpr.Etempvar _ _ (.Vptr c.connB c.connO) (hT.get (by temps_get))) rfl
                  (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl EvalExprlist.nil)))
              (fun _ he => ⟨rfl, he⟩) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))) ?_
        refine triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'2 _ (Val.ofBool (!cfg)) ?_
        intro le m hp hT _ _
        exact EvalExpr.Ecast _ _ _ _
          (EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (notbool_ofBool cfg m))
          (cast_ofBool_bool _ m)
    case c2 =>
      refine triple_if_local ge _ _ emptyEnv _ (H c) _ (!cfg) _ _ _
        (fun le m hp hT _ _ =>
          ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), boolVal_ofBool_tint _ m⟩) ?_
      cases cfg
      · rw [if_pos (show (!false) = true from rfl)]
        refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_nop_loop ge _ _ _) ?_
        exact return_const ge _ _ _ _ _ _ _ (Val.ofBool false) (fun _ => rfl)
          (fun hp hH => ⟨by simp [H5.Case5.sslConfig, input, hn], hH⟩)
      · rw [if_neg (show ¬((!true) = true) from by decide)]
        exact skip_end ge _ _ _ _ _ _ (by simp [H5.Case5.sslConfig, input, hn])

end Case5C
