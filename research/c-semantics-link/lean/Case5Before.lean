/-
Case 5（CURL-CVE-2026-86411）: 修正後の `url_match_ssl_use`（curl 72352daba0）。

証明すること: C の関数は、H5 のモデルの `sslUseB` と同じ値を返す（`ssl_use_before`）。
呼ばれる側の外部関数2つは、仕様（`sslSpec`・`cfgSpec`）を満たすことを仮定として受け取る。
-/
import GenCase5Before
import Case5After
open CC CC.Sep CC.HProp
open Case5_before

set_option maxRecDepth 20000

namespace Case5C

/-- 修正前の `url_match_ssl_use` の仕様: 戻り値は H5 の `sslUseB`、メモリは変えない。 -/
def useSpecB (c : Ctx) (ssl cfg : Bool) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _connectdata noattr), tptr (Ty.Tstruct _url_conn_match noattr)]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.connB c.connO, .Vptr c.mB c.mO] ∧ H c hp
  post := fun v hp => v = Val.ofBool (H5.Case5.sslUseB (input c ssl cfg)) ∧ H c hp
  measure := fun _ => 0

theorem use_entry_wf_b :
    listNorepet (varNames f_url_match_ssl_use.fn_vars)
    ∧ listNorepet (varNames f_url_match_ssl_use.fn_params)
    ∧ listDisjoint (varNames f_url_match_ssl_use.fn_params)
        (varNames f_url_match_ssl_use.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- 修正前と修正後のプログラムの composite 環境は同じ（構造体の定義が同じため）。 -/
theorem cenv_same : prog.prog_comp_env = Case5_after.prog.prog_comp_env := rfl

theorem ssl_use_before (ge : CGenv) (c : Ctx) (ssl cfg : Bool)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true)
    (bSsl bGpf : Block) (fdSsl : FunDef)
    (hsSsl : Genv.findSymbol ge.genv_genv _Curl_conn_is_ssl = some bSsl)
    (hsGpf : Genv.findSymbol ge.genv_genv _get_protocol_family = some bGpf)
    (hfSsl : FuncPtr ge bSsl fdSsl)
    (hfGpf : FuncPtr ge bGpf (.Internal Case5_after.f_get_protocol_family))
    (htySsl : typeOfFundef fdSsl
      = .Tfunction (sslSpec c ssl).tyargs (sslSpec c ssl).tyres (sslSpec c ssl).cc)
    (hSsl : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdSsl (sslSpec c ssl) vs)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_url_match_ssl_use) (useSpecB c ssl cfg) vs := by
  by_cases hvs : vs = [.Vptr c.connB c.connO, .Vptr c.mB c.mO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  have hcenv' : ge.genv_cenv = Case5_after.prog.prog_comp_env := hcenv.trans cenv_same
  obtain ⟨hnv, hnp, hdisj⟩ := use_entry_wf_b
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) f_url_match_ssl_use _ _
    (LocalSt emptyEnv [(_m, .Vptr c.mB c.mO), (_conn, .Vptr c.connB c.connO)] (H c))
    (fun m => ?_) ?_
  · refine ⟨PTree.set _m (.Vptr c.mB c.mO)
              (PTree.set _conn (.Vptr c.connB c.connO)
                (createUndefTemps f_url_match_ssl_use.fn_temps)),
            FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    refine ⟨rfl, TempsHold_cons (PTree.gss _ _ _) (TempsHold_cons ?_ (TempsHold_nil _)), hpre.2⟩
    exact (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)
  -- 本体 = { … } ; return 1;
  refine triple_seq ge _ _ _
    (fun e _ hp => e = emptyEnv ∧ H5.Case5.sslUseB (input c ssl cfg) = true ∧ H c hp)
    _ _ _ ?body ?ret1
  case ret1 =>
    -- return 1;  ここに来るのは sslUseB = true のときだけ
    refine triple_pre ge _ _
      (P := LocalSt emptyEnv [] (fun hp => H5.Case5.sslUseB (input c ssl cfg) = true ∧ H c hp))
      (fun e le hp ⟨he, hφ, hH⟩ => ⟨he, TempsHold_nil _, hφ, hH⟩) ?_
    exact triple_return_local ge _ _ [] _ _ _ (.Vint (Integers.Int.repr 1)) (Val.ofBool true)
      (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _) (fun _ => rfl)
      (fun hp ⟨hφ, hH⟩ => ⟨by rw [hφ], hH⟩)
  case body =>
  -- t'6 = m->needle; t'7 = t'6->scheme; t'8 = t'7->flags
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'5 _ (.Vptr c.ndlB c.ndlO)
      (fun le m hp hT hH hag =>
        eval_field (hT.get (by temps_get)) (hcenv' ▸ co_match) (hcenv' ▸ off_needle) rfl
          (H_loads hpr hH hag).needle)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'6 _ (.Vptr c.nschB c.nschO)
      (fun le m hp hT hH hag =>
        eval_field (hT.get (by temps_get)) (hcenv' ▸ co_conn) (hcenv' ▸ off_scheme) rfl
          (H_loads hpr hH hag).nsch)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'7 _ (.Vint c.flags)
      (fun le m hp hT hH hag =>
        eval_field (hT.get (by temps_get)) (hcenv' ▸ co_scheme) (hcenv' ▸ off_flags) rfl
          (H_loads hpr hH hag).flags)) ?_
  -- if (t'8 & PROTOPT_SSL)
  refine triple_if_local ge _ _ emptyEnv _ (H c) _ (flagBit c.flags 0) _ _ _
    (fun le m hp hT _ _ => ⟨_, eval_flag0 (hT.get (by temps_get)), rfl⟩) ?_
  cases hn : flagBit c.flags 0
  · -- needle は SSL でない
    rw [if_neg Bool.false_ne_true]
    -- t'5 = Curl_conn_is_ssl(conn, 0)
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (call_fwd ge _ _ (sslSpec c ssl) _t'4 _ _ emptyEnv _ emp (H c) emp (H c) (H c)
        [.Vptr c.connB c.connO, .Vint (Integers.Int.repr 0)] (Val.ofBool ssl) bSsl fdSsl
        hSsl hfSsl htySsl rfl (fun _ _ _ => eval_callee_global rfl hsSsl rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vptr c.connB c.connO) (hT.get (by temps_get))) rfl
          (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl EvalExprlist.nil))
        (fun _ he => ⟨rfl, he⟩) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _)) ?_
    refine triple_if_local ge _ _ emptyEnv _ (H c) _ ssl _ _ _
      (fun le m hp hT _ _ =>
        ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), boolVal_ofBool_tbool ssl m⟩) ?_
    cases ssl
    · -- conn も SSL でない: t'9 = m->require_tls; if (t'9) return 0;
      rw [if_neg Bool.false_ne_true]
      refine triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'8 _
          (.Vint (Cop.bitfieldExtract .I32 .Unsigned 1 1 c.bits))
          (fun le m hp hT hH hag =>
            eval_bitfield (hT.get (by temps_get)) (hcenv' ▸ co_match) (hcenv' ▸ off_require_tls)
              (by decide) (by decide) (H_loads hpr hH hag).bits)) ?_
      refine triple_if_local ge _ _ emptyEnv _ (H c) _ (bitOf c.bits 1) _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩) ?_
      cases hq : bitOf c.bits 1
      · rw [if_neg Bool.false_ne_true]
        exact skip_end ge _ _ _ _ _ _ (by simp [H5.Case5.sslUseB, input, hn, hq])
      · rw [if_pos rfl]
        exact return_const ge _ _ _ _ _ _ _ (Val.ofBool false) (fun _ => rfl)
          (fun hp hH => ⟨by simp [H5.Case5.sslUseB, input, hn, hq], hH⟩)
    · -- conn は SSL（TLS の接続を平文の要求に再利用しようとしている）
      rw [if_pos rfl]
      cases hr : flagBit c.flags 15
      · -- PROTOPT_SSL_REUSE が無い: t'2 = 1 → return 0
        refine triple_seq_fwd ge _ _ _ ?Qa _ _ _ ?h1a ?h2a
        case h1a =>
          refine triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'9 _ (.Vptr c.ndlB c.ndlO)
              (fun le m hp hT hH hag =>
                eval_field (hT.get (by temps_get)) (hcenv' ▸ co_match) (hcenv' ▸ off_needle) rfl
                  (H_loads hpr hH hag).needle)) ?_
          refine triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'10 _ (.Vptr c.nschB c.nschO)
              (fun le m hp hT hH hag =>
                eval_field (hT.get (by temps_get)) (hcenv' ▸ co_conn) (hcenv' ▸ off_scheme) rfl
                  (H_loads hpr hH hag).nsch)) ?_
          refine triple_seq_fwd ge _ _ _ _ _ _ _
            (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'11 _ (.Vint c.flags)
              (fun le m hp hT hH hag =>
                eval_field (hT.get (by temps_get)) (hcenv' ▸ co_scheme) (hcenv' ▸ off_flags) rfl
                  (H_loads hpr hH hag).flags)) ?_
          refine triple_if_local ge _ _ emptyEnv _ (H c) _ true _ _ _
            (fun le m hp hT _ _ =>
              ⟨_, eval_notflag15 (hT.get (by temps_get)), by rw [hr]; rfl⟩) ?_
          rw [if_pos rfl]
          exact triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'2 _ (.Vint (Integers.Int.repr 1))
            (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)
        case h2a =>
          refine triple_if_local ge _ _ emptyEnv _ (H c) _ true _ _ _
            (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩) ?_
          rw [if_pos rfl]
          exact return_const ge _ _ _ _ _ _ _ (Val.ofBool false) (fun _ => rfl)
            (fun hp hH => ⟨by simp [H5.Case5.sslUseB, input, hn, hr], hH⟩)
      · -- PROTOPT_SSL_REUSE がある: t'2 = (get_protocol_family(conn->scheme) != needle->scheme->protocol)
        cases hs : Integers.Int64.eq c.fam c.proto
        · -- 族が違う → return 0
          refine triple_seq_fwd ge _ _ _ ?Qb _ _ _ ?h1b ?h2b
          case h1b =>
            refine triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'9 _ (.Vptr c.ndlB c.ndlO)
                (fun le m hp hT hH hag =>
                  eval_field (hT.get (by temps_get)) (hcenv' ▸ co_match) (hcenv' ▸ off_needle) rfl
                    (H_loads hpr hH hag).needle)) ?_
            refine triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'10 _ (.Vptr c.nschB c.nschO)
                (fun le m hp hT hH hag =>
                  eval_field (hT.get (by temps_get)) (hcenv' ▸ co_conn) (hcenv' ▸ off_scheme) rfl
                    (H_loads hpr hH hag).nsch)) ?_
            refine triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'11 _ (.Vint c.flags)
                (fun le m hp hT hH hag =>
                  eval_field (hT.get (by temps_get)) (hcenv' ▸ co_scheme) (hcenv' ▸ off_flags) rfl
                    (H_loads hpr hH hag).flags)) ?_
            refine triple_if_local ge _ _ emptyEnv _ (H c) _ false _ _ _
              (fun le m hp hT _ _ =>
                ⟨_, eval_notflag15 (hT.get (by temps_get)), by rw [hr]; rfl⟩) ?_
            rw [if_neg Bool.false_ne_true]
            refine triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_seq_fwd ge _ _ _ _ _ _ _
                (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'15 _ (.Vptr c.cschB c.cschO)
                  (fun le m hp hT hH hag =>
                    eval_field (hT.get (by temps_get)) (hcenv' ▸ co_conn) (hcenv' ▸ off_scheme) rfl
                      (H_loads hpr hH hag).csch))
                (call_fwd ge _ _ (gpfSpec c) _t'3 _ _ emptyEnv _ (H c) emp (H c) (H c) (H c)
                  [.Vptr c.cschB c.cschO] (.Vlong c.fam) bGpf _ (gpf_satisfies ge c hcenv' hpr) hfGpf rfl rfl
                  (fun _ _ _ => eval_callee_global rfl hsGpf rfl)
                  (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
                    (EvalExpr.Etempvar _ _ (.Vptr c.cschB c.cschO) (hT.get (by temps_get))) rfl EvalExprlist.nil)
                  (fun _ hh => ⟨rfl, hh⟩) (fun _ _ hp => hp) (sep_emp_eq _).symm (sep_emp_eq _))) ?_
            refine triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'12 _ (.Vptr c.ndlB c.ndlO)
                (fun le m hp hT hH hag =>
                  eval_field (hT.get (by temps_get)) (hcenv' ▸ co_match) (hcenv' ▸ off_needle) rfl
                    (H_loads hpr hH hag).needle)) ?_
            refine triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'13 _ (.Vptr c.nschB c.nschO)
                (fun le m hp hT hH hag =>
                  eval_field (hT.get (by temps_get)) (hcenv' ▸ co_conn) (hcenv' ▸ off_scheme) rfl
                    (H_loads hpr hH hag).nsch)) ?_
            refine triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'14 _ (.Vlong c.proto)
                (fun le m hp hT hH hag =>
                  eval_field (hT.get (by temps_get)) (hcenv' ▸ co_scheme) (hcenv' ▸ off_protocol) rfl
                    (H_loads hpr hH hag).proto)) ?_
            refine triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'2 _
              (Val.ofBool (!Integers.Int64.eq c.fam c.proto)) ?_
            intro le m hp hT _ _
            exact eval_ne_cast (hT.get (by temps_get)) (hT.get (by temps_get))
          case h2b =>
            refine triple_if_local ge _ _ emptyEnv _ (H c) _ true _ _ _
              (fun le m hp hT _ _ =>
                ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
                 by rw [hs]; exact boolVal_ofBool_tint _ m⟩) ?_
            rw [if_pos rfl]
            exact return_const ge _ _ _ _ _ _ _ (Val.ofBool false) (fun _ => rfl)
              (fun hp hH => ⟨by simp [H5.Case5.sslUseB, input, hn, hr, hs], hH⟩)
        · -- 族が同じ → 再利用する（修正前は、ここで SSL の設定を確かめない）
          refine triple_seq_fwd ge _ _ _ ?Qc _ _ _ ?h1c ?h2c
          case h1c =>
            refine triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'9 _ (.Vptr c.ndlB c.ndlO)
                (fun le m hp hT hH hag =>
                  eval_field (hT.get (by temps_get)) (hcenv' ▸ co_match) (hcenv' ▸ off_needle) rfl
                    (H_loads hpr hH hag).needle)) ?_
            refine triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'10 _ (.Vptr c.nschB c.nschO)
                (fun le m hp hT hH hag =>
                  eval_field (hT.get (by temps_get)) (hcenv' ▸ co_conn) (hcenv' ▸ off_scheme) rfl
                    (H_loads hpr hH hag).nsch)) ?_
            refine triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'11 _ (.Vint c.flags)
                (fun le m hp hT hH hag =>
                  eval_field (hT.get (by temps_get)) (hcenv' ▸ co_scheme) (hcenv' ▸ off_flags) rfl
                    (H_loads hpr hH hag).flags)) ?_
            refine triple_if_local ge _ _ emptyEnv _ (H c) _ false _ _ _
              (fun le m hp hT _ _ =>
                ⟨_, eval_notflag15 (hT.get (by temps_get)), by rw [hr]; rfl⟩) ?_
            rw [if_neg Bool.false_ne_true]
            refine triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_seq_fwd ge _ _ _ _ _ _ _
                (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'15 _ (.Vptr c.cschB c.cschO)
                  (fun le m hp hT hH hag =>
                    eval_field (hT.get (by temps_get)) (hcenv' ▸ co_conn) (hcenv' ▸ off_scheme) rfl
                      (H_loads hpr hH hag).csch))
                (call_fwd ge _ _ (gpfSpec c) _t'3 _ _ emptyEnv _ (H c) emp (H c) (H c) (H c)
                  [.Vptr c.cschB c.cschO] (.Vlong c.fam) bGpf _ (gpf_satisfies ge c hcenv' hpr) hfGpf rfl rfl
                  (fun _ _ _ => eval_callee_global rfl hsGpf rfl)
                  (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
                    (EvalExpr.Etempvar _ _ (.Vptr c.cschB c.cschO) (hT.get (by temps_get))) rfl EvalExprlist.nil)
                  (fun _ hh => ⟨rfl, hh⟩) (fun _ _ hp => hp) (sep_emp_eq _).symm (sep_emp_eq _))) ?_
            refine triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'12 _ (.Vptr c.ndlB c.ndlO)
                (fun le m hp hT hH hag =>
                  eval_field (hT.get (by temps_get)) (hcenv' ▸ co_match) (hcenv' ▸ off_needle) rfl
                    (H_loads hpr hH hag).needle)) ?_
            refine triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'13 _ (.Vptr c.nschB c.nschO)
                (fun le m hp hT hH hag =>
                  eval_field (hT.get (by temps_get)) (hcenv' ▸ co_conn) (hcenv' ▸ off_scheme) rfl
                    (H_loads hpr hH hag).nsch)) ?_
            refine triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'14 _ (.Vlong c.proto)
                (fun le m hp hT hH hag =>
                  eval_field (hT.get (by temps_get)) (hcenv' ▸ co_scheme) (hcenv' ▸ off_protocol) rfl
                    (H_loads hpr hH hag).proto)) ?_
            refine triple_set_local_fwd ge _ _ emptyEnv _ (H c) _t'2 _
              (Val.ofBool (!Integers.Int64.eq c.fam c.proto)) ?_
            intro le m hp hT _ _
            exact eval_ne_cast (hT.get (by temps_get)) (hT.get (by temps_get))
          case h2c =>
            refine triple_if_local ge _ _ emptyEnv _ (H c) _ false _ _ _
              (fun le m hp hT _ _ =>
                ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
                 by rw [hs]; exact boolVal_ofBool_tint _ m⟩) ?_
            rw [if_neg Bool.false_ne_true]
            exact skip_end ge _ _ _ _ _ _ (by simp [H5.Case5.sslUseB, input, hn, hr, hs])
  · -- needle は SSL: t'1 = Curl_conn_is_ssl(conn, 0); if (!t'1) return 0;
    rw [if_pos rfl]
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (call_fwd ge _ _ (sslSpec c ssl) _t'1 _ _ emptyEnv _ emp (H c) emp (H c) (H c)
        [.Vptr c.connB c.connO, .Vint (Integers.Int.repr 0)] (Val.ofBool ssl) bSsl fdSsl
        hSsl hfSsl htySsl rfl (fun _ _ _ => eval_callee_global rfl hsSsl rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vptr c.connB c.connO) (hT.get (by temps_get))) rfl
          (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl EvalExprlist.nil))
        (fun _ he => ⟨rfl, he⟩) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _)) ?_
    refine triple_if_local ge _ _ emptyEnv _ (H c) _ (!ssl) _ _ _
      (fun le m hp hT _ _ =>
        ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
            (notbool_ofBool ssl m), boolVal_ofBool_tint _ m⟩) ?_
    cases ssl
    · rw [if_pos (show (!false) = true from rfl)]
      exact return_const ge _ _ _ _ _ _ _ (Val.ofBool false) (fun _ => rfl)
        (fun hp hH => ⟨by simp [H5.Case5.sslUseB, input, hn], hH⟩)
    · rw [if_neg (show ¬((!true) = true) from by decide)]
      exact skip_end ge _ _ _ _ _ _ (by simp [H5.Case5.sslUseB, input, hn])

end Case5C
