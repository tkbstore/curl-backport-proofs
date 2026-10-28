/-
Case 2: `url_match_auth_nego` の本体の証明（`auth_nego_eq`）。

証明の本文は scratchpad の生成スクリプトで経路ごとに組み立てたもの（分岐ごとに、読む値・呼ぶ関数・戻り値が決まる）。
経路: 前半（`http_negotiate_state` の検査）は want × negotiated × creds × cs × oe の9通り、
後半（`want_nego_http` による受け入れ）は want × negotiated の4通り。
-/
import Case2Nego
open CC CC.Sep CC.HProp
open Case2_after
open Case5C (addr call_fwd RR return_const skip_end skip_fall boolVal_ofBool_tint boolVal_ofBool_tbool
  notbool_ofBool eval_bitfield eval_field bitOf cast_ofBool_bool cast_int_bool)
open Case4C (IsPtr cast_ptr eval_deref_temp lv_field triple_pure_pre)

set_option maxRecDepth 20000

namespace Case2C

open H5.Case2 (Verdict matchNego)

theorem auth_nego_eq (ge : CGenv) (c : Ctx2) (foundV : Val) (word : Integers.Int) (cs oe : Bool)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hpw : permOrder c.pm .Writable = true)
    (hptr : Ptrs2 c) (hprox : bitOf word 2 = false)
    (bCs bPe : Block) (fdCs fdPe : FunDef)
    (hsCs : Genv.findSymbol ge.genv_genv _Curl_creds_same = some bCs)
    (hsPe : Genv.findSymbol ge.genv_genv _Curl_peer_equal = some bPe)
    (hfCs : FuncPtr ge bCs fdCs) (hfPe : FuncPtr ge bPe fdPe)
    (htyCs : typeOfFundef fdCs
      = .Tfunction (credsSpec cs).tyargs (credsSpec cs).tyres (credsSpec cs).cc)
    (htyPe : typeOfFundef fdPe
      = .Tfunction (peerSpec oe).tyargs (peerSpec oe).tyres (peerSpec oe).cc)
    (hCs : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdCs (credsSpec cs) vs)
    (hPe : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdPe (peerSpec oe) vs)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_url_match_auth_nego)
      (negoSpec c foundV word cs oe) vs := by
  by_cases hvs : vs = [.Vptr c.connB c.connO, .Vptr c.mB c.mO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := nego_entry_wf
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) f_url_match_auth_nego _ _
    (LocalSt emptyEnv [(_m, .Vptr c.mB c.mO), (_conn, .Vptr c.connB c.connO)] (H2 c foundV word))
    (fun m => ?_) ?_
  · refine ⟨PTree.set _m (.Vptr c.mB c.mO)
              (PTree.set _conn (.Vptr c.connB c.connO)
                (createUndefTemps f_url_match_auth_nego.fn_temps)),
            FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ?_⟩
    refine ⟨rfl, TempsHold_cons (PTree.gss _ _ _) (TempsHold_cons ?_ (TempsHold_nil _)), hpre.2⟩
    exact (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)
  cases hw : bitOf word 1 <;> cases hng : Integers.Int.eq c.ns Integers.Int.zero
  · refine triple_seq ge _ _ _ (fun e le hp => vdOf c word cs oe ≠ .reject ∧ LocalSt emptyEnv [(_m, .Vptr c.mB c.mO), (_conn, .Vptr c.connB c.connO)] (H2 c foundV word) e le hp) _ _ _ ?nff ?tff
    case nff =>
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'17 _ (.Vint c.ns) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_nego) rfl (H2_loads hpr hpn hptr hH hag).ns)) ?_
      refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (EvalExpr.Econst_int _ _) (ne_zero_eval _ _ _), (boolVal_ofBool_tint _ m).trans (by rw [hng]; rfl)⟩) ?_
      rw [if_pos rfl]
      apply Sep.triple_seq_fwd
      · apply Sep.triple_seq_fwd
        · refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'29 _ (.Vint (Cop.bitfieldExtract .I32 .Unsigned 1 1 word)) (fun le m hp hT hH hag => eval_bitfield (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_want) (by decide) (by decide) (H2_loads hpr hpn hptr hH hag).word)) ?_
          refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (notbool_int _ m), (notbool_bit_val word 1 m).trans (by rw [hw]; rfl)⟩) ?_
          rw [if_pos rfl]
          exact (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'1 _ (.Vint (Integers.Int.repr 1)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))
        · refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩) ?_
          rw [if_pos rfl]
          exact (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'3 _ (.Vint (Integers.Int.repr 1)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))
      · refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩) ?_
        rw [if_pos rfl]
        exact return_const ge _ _ _ _ _ _ _ (Val.ofBool false) (fun _ => rfl)
          (fun hp hH => post_of c foundV word cs oe _ hp .reject (by simp [vdOf, matchNego, negInput, hw, hng]) rfl hH)
    case tff =>
      refine triple_pure_pre ge _ _ _ _ _ _ (fun hφ => ?_)
      exact absurd hφ (by simp [vdOf, matchNego, negInput, hw, hng])
  · refine triple_seq ge _ _ _ (fun e le hp => vdOf c word cs oe ≠ .reject ∧ LocalSt emptyEnv [(_m, .Vptr c.mB c.mO), (_conn, .Vptr c.connB c.connO)] (H2 c foundV word) e le hp) _ _ _ ?nft ?tft
    case nft =>
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'17 _ (.Vint c.ns) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_nego) rfl (H2_loads hpr hpn hptr hH hag).ns)) ?_
      refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (EvalExpr.Econst_int _ _) (ne_zero_eval _ _ _), (boolVal_ofBool_tint _ m).trans (by rw [hng]; rfl)⟩) ?_
      rw [if_neg Bool.false_ne_true]
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'18 _ (.Vint (Cop.bitfieldExtract .I32 .Unsigned 1 1 word)) (fun le m hp hT hH hag => eval_bitfield (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_want) (by decide) (by decide) (H2_loads hpr hpn hptr hH hag).word)) ?_
      refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), (boolVal_bit_val word 1 m).trans (by rw [hw])⟩) ?_
      rw [if_neg Bool.false_ne_true]
      exact fall_to ge _ _ _ [(_m, .Vptr c.mB c.mO), (_conn, .Vptr c.connB c.connO)] _ _ _ (fun p hp => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl | rfl <;> temps_get)
        (by simp [vdOf, matchNego, negInput, hw, hng])
    case tft =>
      refine triple_pure_pre ge _ _ _ _ _ _ (fun hφ => ?_)
      apply Sep.triple_seq
      · apply Sep.triple_seq_fwd
        · refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'15 _ (.Vint (Cop.bitfieldExtract .I32 .Unsigned 1 1 word)) (fun le m hp hT hH hag => eval_bitfield (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_want) (by decide) (by decide) (H2_loads hpr hpn hptr hH hag).word)) ?_
          refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), (boolVal_bit_val word 1 m).trans (by rw [hw])⟩) ?_
          rw [if_neg Bool.false_ne_true]
          refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'16 _ (.Vint (Cop.bitfieldExtract .I32 .Unsigned 2 1 word)) (fun le m hp hT hH hag => eval_bitfield (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_proxy) (by decide) (by decide) (H2_loads hpr hpn hptr hH hag).word)) ?_
          refine triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'10 _ (Val.ofBool (bitOf word 2)) ?_
          intro le m hp hT hH hag
          exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _t'16 _ _ (hT.get (by temps_get))) (cast_int_bool _ m)
        · refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), (boolVal_ofBool_tint _ m).trans (by rw [hprox])⟩) ?_
          rw [if_neg Bool.false_ne_true]
          exact skip_fall ge _ _ _ _
      · have hvd : vdOf c word cs oe = .accept := by simp [vdOf, matchNego, negInput, hw, hng]
        exact return_const ge _ _ _ _ _ _ _ (Val.ofBool true) (fun _ => rfl)
          (fun hp hH => post_of c foundV word cs oe _ hp _ hvd rfl hH)
  · refine triple_seq ge _ _ _ (fun e le hp => vdOf c word cs oe ≠ .reject ∧ LocalSt emptyEnv [(_m, .Vptr c.mB c.mO), (_conn, .Vptr c.connB c.connO)] (H2 c foundV word) e le hp) _ _ _ ?ntf ?ttf
    case ntf =>
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'17 _ (.Vint c.ns) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_nego) rfl (H2_loads hpr hpn hptr hH hag).ns)) ?_
      refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (EvalExpr.Econst_int _ _) (ne_zero_eval _ _ _), (boolVal_ofBool_tint _ m).trans (by rw [hng]; rfl)⟩) ?_
      rw [if_pos rfl]
      cases cs
      · -- creds が違う
        apply Sep.triple_seq_fwd
        · apply Sep.triple_seq_fwd
          · refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'29 _ (.Vint (Cop.bitfieldExtract .I32 .Unsigned 1 1 word)) (fun le m hp hT hH hag => eval_bitfield (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_want) (by decide) (by decide) (H2_loads hpr hpn hptr hH hag).word)) ?_
            refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (notbool_int _ m), (notbool_bit_val word 1 m).trans (by rw [hw]; rfl)⟩) ?_
            rw [if_neg Bool.false_ne_true]
            refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'30 _ (c.credsV) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_creds) rfl (H2_loads hpr hpn hptr hH hag).creds)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'31 _ (.Vptr c.dataB c.dataO) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_data) rfl (H2_loads hpr hpn hptr hH hag).data)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'32 _ (c.scredsV) (fun le m hp hT hH hag => eval_state_field hcenv (hT.get (by temps_get)) off_screds rfl (H2_loads hpr hpn hptr hH hag).screds)) (call_fwd ge _ _ (credsSpec false) _t'2 _ _ emptyEnv _ emp (H2 c foundV word) emp (H2 c foundV word) (H2 c foundV word) [c.credsV, c.scredsV] (Val.ofBool false) bCs fdCs hCs hfCs htyCs rfl (fun _ _ _ => eval_callee_global rfl hsCs rfl) (fun le m hT => (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'30 _ (c.credsV) (hT.get (by temps_get))) (cast_ptr (creds_isPtr hptr) _ _ m) (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'32 _ (c.scredsV) (hT.get (by temps_get))) (cast_ptr hptr.screds _ _ m) EvalExprlist.nil))) (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))))) ?_
            refine triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'1 _ (Val.ofBool (!false)) ?_
            intro le m hp hT hH hag
            exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _t'2 _ _ (hT.get (by temps_get))) (notbool_ofBool false m)) (cast_ofBool_bool _ m)
          · refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), boolVal_ofBool_tint _ m⟩) ?_
            rw [if_pos rfl]
            exact (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'3 _ (.Vint (Integers.Int.repr 1)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))
        · refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩) ?_
          rw [if_pos rfl]
          exact return_const ge _ _ _ _ _ _ _ (Val.ofBool false) (fun _ => rfl)
            (fun hp hH => post_of c foundV word false oe _ hp .reject (by simp [vdOf, matchNego, negInput, hw, hng]) rfl hH)
      · cases oe
        · apply Sep.triple_seq_fwd
          · apply Sep.triple_seq_fwd
            · refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'29 _ (.Vint (Cop.bitfieldExtract .I32 .Unsigned 1 1 word)) (fun le m hp hT hH hag => eval_bitfield (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_want) (by decide) (by decide) (H2_loads hpr hpn hptr hH hag).word)) ?_
              refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (notbool_int _ m), (notbool_bit_val word 1 m).trans (by rw [hw]; rfl)⟩) ?_
              rw [if_neg Bool.false_ne_true]
              refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'30 _ (c.credsV) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_creds) rfl (H2_loads hpr hpn hptr hH hag).creds)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'31 _ (.Vptr c.dataB c.dataO) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_data) rfl (H2_loads hpr hpn hptr hH hag).data)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'32 _ (c.scredsV) (fun le m hp hT hH hag => eval_state_field hcenv (hT.get (by temps_get)) off_screds rfl (H2_loads hpr hpn hptr hH hag).screds)) (call_fwd ge _ _ (credsSpec true) _t'2 _ _ emptyEnv _ emp (H2 c foundV word) emp (H2 c foundV word) (H2 c foundV word) [c.credsV, c.scredsV] (Val.ofBool true) bCs fdCs hCs hfCs htyCs rfl (fun _ _ _ => eval_callee_global rfl hsCs rfl) (fun le m hT => (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'30 _ (c.credsV) (hT.get (by temps_get))) (cast_ptr (creds_isPtr hptr) _ _ m) (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'32 _ (c.scredsV) (hT.get (by temps_get))) (cast_ptr hptr.screds _ _ m) EvalExprlist.nil))) (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))))) ?_
              refine triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'1 _ (Val.ofBool (!true)) ?_
              intro le m hp hT hH hag
              exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _t'2 _ _ (hT.get (by temps_get))) (notbool_ofBool true m)) (cast_ofBool_bool _ m)
            · refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), boolVal_ofBool_tint _ m⟩) ?_
              rw [if_neg Bool.false_ne_true]
              refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'26 _ (c.corigV) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_creds_origin) rfl (H2_loads hpr hpn hptr hH hag).corig)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'27 _ (.Vptr c.dataB c.dataO) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_data) rfl (H2_loads hpr hpn hptr hH hag).data)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'28 _ (c.originV) (fun le m hp hT hH hag => eval_state_field hcenv (hT.get (by temps_get)) off_origin rfl (H2_loads hpr hpn hptr hH hag).origin)) (call_fwd ge _ _ (peerSpec false) _t'4 _ _ emptyEnv _ emp (H2 c foundV word) emp (H2 c foundV word) (H2 c foundV word) [c.corigV, c.originV] (Val.ofBool false) bPe fdPe hPe hfPe htyPe rfl (fun _ _ _ => eval_callee_global rfl hsPe rfl) (fun le m hT => (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'26 _ (c.corigV) (hT.get (by temps_get))) (cast_ptr hptr.corig _ _ m) (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'28 _ (c.originV) (hT.get (by temps_get))) (cast_ptr hptr.origin _ _ m) EvalExprlist.nil))) (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))))) ?_
              refine triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'3 _ (Val.ofBool (!false)) ?_
              intro le m hp hT hH hag
              exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _t'4 _ _ (hT.get (by temps_get))) (notbool_ofBool false m)) (cast_ofBool_bool _ m)
          · refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), boolVal_ofBool_tint _ m⟩) ?_
            rw [if_pos rfl]
            exact return_const ge _ _ _ _ _ _ _ (Val.ofBool false) (fun _ => rfl)
              (fun hp hH => post_of c foundV word true false _ hp .reject (by simp [vdOf, matchNego, negInput, hw, hng]) rfl hH)
        · apply Sep.triple_seq_fwd
          · apply Sep.triple_seq_fwd
            · refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'29 _ (.Vint (Cop.bitfieldExtract .I32 .Unsigned 1 1 word)) (fun le m hp hT hH hag => eval_bitfield (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_want) (by decide) (by decide) (H2_loads hpr hpn hptr hH hag).word)) ?_
              refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (notbool_int _ m), (notbool_bit_val word 1 m).trans (by rw [hw]; rfl)⟩) ?_
              rw [if_neg Bool.false_ne_true]
              refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'30 _ (c.credsV) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_creds) rfl (H2_loads hpr hpn hptr hH hag).creds)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'31 _ (.Vptr c.dataB c.dataO) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_data) rfl (H2_loads hpr hpn hptr hH hag).data)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'32 _ (c.scredsV) (fun le m hp hT hH hag => eval_state_field hcenv (hT.get (by temps_get)) off_screds rfl (H2_loads hpr hpn hptr hH hag).screds)) (call_fwd ge _ _ (credsSpec true) _t'2 _ _ emptyEnv _ emp (H2 c foundV word) emp (H2 c foundV word) (H2 c foundV word) [c.credsV, c.scredsV] (Val.ofBool true) bCs fdCs hCs hfCs htyCs rfl (fun _ _ _ => eval_callee_global rfl hsCs rfl) (fun le m hT => (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'30 _ (c.credsV) (hT.get (by temps_get))) (cast_ptr (creds_isPtr hptr) _ _ m) (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'32 _ (c.scredsV) (hT.get (by temps_get))) (cast_ptr hptr.screds _ _ m) EvalExprlist.nil))) (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))))) ?_
              refine triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'1 _ (Val.ofBool (!true)) ?_
              intro le m hp hT hH hag
              exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _t'2 _ _ (hT.get (by temps_get))) (notbool_ofBool true m)) (cast_ofBool_bool _ m)
            · refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), boolVal_ofBool_tint _ m⟩) ?_
              rw [if_neg Bool.false_ne_true]
              refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'26 _ (c.corigV) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_creds_origin) rfl (H2_loads hpr hpn hptr hH hag).corig)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'27 _ (.Vptr c.dataB c.dataO) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_data) rfl (H2_loads hpr hpn hptr hH hag).data)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'28 _ (c.originV) (fun le m hp hT hH hag => eval_state_field hcenv (hT.get (by temps_get)) off_origin rfl (H2_loads hpr hpn hptr hH hag).origin)) (call_fwd ge _ _ (peerSpec true) _t'4 _ _ emptyEnv _ emp (H2 c foundV word) emp (H2 c foundV word) (H2 c foundV word) [c.corigV, c.originV] (Val.ofBool true) bPe fdPe hPe hfPe htyPe rfl (fun _ _ _ => eval_callee_global rfl hsPe rfl) (fun le m hT => (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'26 _ (c.corigV) (hT.get (by temps_get))) (cast_ptr hptr.corig _ _ m) (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'28 _ (c.originV) (hT.get (by temps_get))) (cast_ptr hptr.origin _ _ m) EvalExprlist.nil))) (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))))) ?_
              refine triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'3 _ (Val.ofBool (!true)) ?_
              intro le m hp hT hH hag
              exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _t'4 _ _ (hT.get (by temps_get))) (notbool_ofBool true m)) (cast_ofBool_bool _ m)
          · refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), boolVal_ofBool_tint _ m⟩) ?_
            rw [if_neg Bool.false_ne_true]
            exact fall_to ge _ _ _ [(_m, .Vptr c.mB c.mO), (_conn, .Vptr c.connB c.connO)] _ _ _ (fun p hp => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl | rfl <;> temps_get)
              (by simp [vdOf, matchNego, negInput, hw, hng])
    case ttf =>
      refine triple_pure_pre ge _ _ _ _ _ _ (fun hφ => ?_)
      refine Sep.triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (triple_vacuous ge _ _ _ _)
      apply Sep.triple_seq_fwd
      · refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'15 _ (.Vint (Cop.bitfieldExtract .I32 .Unsigned 1 1 word)) (fun le m hp hT hH hag => eval_bitfield (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_want) (by decide) (by decide) (H2_loads hpr hpn hptr hH hag).word)) ?_
        refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), (boolVal_bit_val word 1 m).trans (by rw [hw])⟩) ?_
        rw [if_pos rfl]
        exact (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'10 _ (.Vint (Integers.Int.repr 1)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))
      · refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩) ?_
        rw [if_pos rfl]
        refine triple_seq_fwd ge _ _ _ _ _ _ _ (assign_found ge c foundV word _ hcenv hpw (by temps_get) (by temps_get)) ?_
        refine triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (triple_vacuous ge _ _ _ _)
        apply Sep.triple_seq_fwd
        · apply Sep.triple_seq_fwd
          · refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c (.Vptr c.connB c.connO) word) _t'13 _ (.Vint (Cop.bitfieldExtract .I32 .Unsigned 1 1 word)) (fun le m hp hT hH hag => eval_bitfield (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_want) (by decide) (by decide) (H2_loads hpr hpn hptr hH hag).word)) ?_
            refine triple_if_local ge _ _ emptyEnv _ (H2 c (.Vptr c.connB c.connO) word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), (boolVal_bit_val word 1 m).trans (by rw [hw])⟩) ?_
            rw [if_pos rfl]
            refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c (.Vptr c.connB c.connO) word) _t'14 _ (.Vint c.ns) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_nego) rfl (H2_loads hpr hpn hptr hH hag).ns)) ?_
            refine triple_set_local_fwd ge _ _ emptyEnv _ (H2 c (.Vptr c.connB c.connO) word) _t'8 _ ((Val.ofBool (!Integers.Int.eq c.ns Integers.Int.zero))) ?_
            intro le m hp hT hH hag
            exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'14 _ _ (hT.get (by temps_get))) (EvalExpr.Econst_int _ _) (ne_zero_eval _ _ _)) (cast_ofBool_bool _ m)
          · refine triple_if_local ge _ _ emptyEnv _ (H2 c (.Vptr c.connB c.connO) word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), (boolVal_ofBool_tint _ m).trans (by rw [hng]; rfl)⟩) ?_
            rw [if_pos rfl]
            exact (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c (.Vptr c.connB c.connO) word) _t'9 _ (.Vint (Integers.Int.repr 1)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))
        · refine triple_if_local ge _ _ emptyEnv _ (H2 c (.Vptr c.connB c.connO) word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩) ?_
          rw [if_pos rfl]
          refine triple_seq_fwd ge _ _ _ _ _ _ _ (assign_force ge c word _ hcenv hpw hpr (by temps_get)) ?_
          have hvd : vdOf c word cs oe = .forceReuse := by
            revert hφ; cases cs <;> cases oe <;> simp [vdOf, matchNego, negInput, hw, hng]
          exact return_const ge _ _ _ _ _ _ _ (Val.ofBool true) (fun _ => rfl)
            (fun hp hH => post_of c foundV word cs oe _ hp _ hvd rfl hH)
  · refine triple_seq ge _ _ _ (fun e le hp => vdOf c word cs oe ≠ .reject ∧ LocalSt emptyEnv [(_m, .Vptr c.mB c.mO), (_conn, .Vptr c.connB c.connO)] (H2 c foundV word) e le hp) _ _ _ ?ntt ?ttt
    case ntt =>
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'17 _ (.Vint c.ns) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_nego) rfl (H2_loads hpr hpn hptr hH hag).ns)) ?_
      refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (EvalExpr.Econst_int _ _) (ne_zero_eval _ _ _), (boolVal_ofBool_tint _ m).trans (by rw [hng]; rfl)⟩) ?_
      rw [if_neg Bool.false_ne_true]
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'18 _ (.Vint (Cop.bitfieldExtract .I32 .Unsigned 1 1 word)) (fun le m hp hT hH hag => eval_bitfield (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_want) (by decide) (by decide) (H2_loads hpr hpn hptr hH hag).word)) ?_
      refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), (boolVal_bit_val word 1 m).trans (by rw [hw])⟩) ?_
      rw [if_pos rfl]
      rcases hptr.creds with hcr | hcr
      · apply Sep.triple_seq_fwd
        · refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'19 _ (c.credsV) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_creds) rfl (H2_loads hpr hpn hptr hH hag).creds)) ?_
          refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ false _ _ _ (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), (boolVal_ptr_creds hptr (H2_loads hpr hpn hptr hH hag).valid).trans (by rw [hcr]; simp)⟩) ?_
          rw [if_neg Bool.false_ne_true]
          exact (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'5 _ (.Vint (Integers.Int.repr 0)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))
        · refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩) ?_
          rw [if_neg Bool.false_ne_true]
          exact fall_to ge _ _ _ [(_m, .Vptr c.mB c.mO), (_conn, .Vptr c.connB c.connO)] _ _ _ (fun p hp => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl | rfl <;> temps_get)
            (by simp [vdOf, matchNego, negInput, hw, hng, hcr])
      · cases cs
        · apply Sep.triple_seq_fwd
          · refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'19 _ (c.credsV) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_creds) rfl (H2_loads hpr hpn hptr hH hag).creds)) ?_
            refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ true _ _ _ (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), (boolVal_ptr_creds hptr (H2_loads hpr hpn hptr hH hag).valid).trans (by rw [hcr]; simp)⟩) ?_
            rw [if_pos rfl]
            refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'23 _ (c.credsV) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_creds) rfl (H2_loads hpr hpn hptr hH hag).creds)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'24 _ (.Vptr c.dataB c.dataO) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_data) rfl (H2_loads hpr hpn hptr hH hag).data)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'25 _ (c.scredsV) (fun le m hp hT hH hag => eval_state_field hcenv (hT.get (by temps_get)) off_screds rfl (H2_loads hpr hpn hptr hH hag).screds)) (call_fwd ge _ _ (credsSpec false) _t'6 _ _ emptyEnv _ emp (H2 c foundV word) emp (H2 c foundV word) (H2 c foundV word) [c.credsV, c.scredsV] (Val.ofBool false) bCs fdCs hCs hfCs htyCs rfl (fun _ _ _ => eval_callee_global rfl hsCs rfl) (fun le m hT => (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'23 _ (c.credsV) (hT.get (by temps_get))) (cast_ptr (creds_isPtr hptr) _ _ m) (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'25 _ (c.scredsV) (hT.get (by temps_get))) (cast_ptr hptr.screds _ _ m) EvalExprlist.nil))) (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))))) ?_
            refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (notbool_ofBool _ m), boolVal_ofBool_tint _ m⟩) ?_
            rw [if_pos rfl]
            refine triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'5 _ (Val.ofBool true) ?_
            intro le m hp hT hH hag
            exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl
          · refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), boolVal_ofBool_tint _ m⟩) ?_
            rw [if_pos rfl]
            exact return_const ge _ _ _ _ _ _ _ (Val.ofBool false) (fun _ => rfl)
              (fun hp hH => post_of c foundV word false oe _ hp .reject (by simp [vdOf, matchNego, negInput, hw, hng, hcr]) rfl hH)
        · cases oe
          · apply Sep.triple_seq_fwd
            · refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'19 _ (c.credsV) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_creds) rfl (H2_loads hpr hpn hptr hH hag).creds)) ?_
              refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ true _ _ _ (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), (boolVal_ptr_creds hptr (H2_loads hpr hpn hptr hH hag).valid).trans (by rw [hcr]; simp)⟩) ?_
              rw [if_pos rfl]
              refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'23 _ (c.credsV) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_creds) rfl (H2_loads hpr hpn hptr hH hag).creds)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'24 _ (.Vptr c.dataB c.dataO) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_data) rfl (H2_loads hpr hpn hptr hH hag).data)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'25 _ (c.scredsV) (fun le m hp hT hH hag => eval_state_field hcenv (hT.get (by temps_get)) off_screds rfl (H2_loads hpr hpn hptr hH hag).screds)) (call_fwd ge _ _ (credsSpec true) _t'6 _ _ emptyEnv _ emp (H2 c foundV word) emp (H2 c foundV word) (H2 c foundV word) [c.credsV, c.scredsV] (Val.ofBool true) bCs fdCs hCs hfCs htyCs rfl (fun _ _ _ => eval_callee_global rfl hsCs rfl) (fun le m hT => (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'23 _ (c.credsV) (hT.get (by temps_get))) (cast_ptr (creds_isPtr hptr) _ _ m) (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'25 _ (c.scredsV) (hT.get (by temps_get))) (cast_ptr hptr.screds _ _ m) EvalExprlist.nil))) (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))))) ?_
              refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (notbool_ofBool _ m), boolVal_ofBool_tint _ m⟩) ?_
              rw [if_neg Bool.false_ne_true]
              refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'20 _ (c.corigV) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_creds_origin) rfl (H2_loads hpr hpn hptr hH hag).corig)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'21 _ (.Vptr c.dataB c.dataO) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_data) rfl (H2_loads hpr hpn hptr hH hag).data)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'22 _ (c.originV) (fun le m hp hT hH hag => eval_state_field hcenv (hT.get (by temps_get)) off_origin rfl (H2_loads hpr hpn hptr hH hag).origin)) (call_fwd ge _ _ (peerSpec false) _t'7 _ _ emptyEnv _ emp (H2 c foundV word) emp (H2 c foundV word) (H2 c foundV word) [c.corigV, c.originV] (Val.ofBool false) bPe fdPe hPe hfPe htyPe rfl (fun _ _ _ => eval_callee_global rfl hsPe rfl) (fun le m hT => (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'20 _ (c.corigV) (hT.get (by temps_get))) (cast_ptr hptr.corig _ _ m) (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'22 _ (c.originV) (hT.get (by temps_get))) (cast_ptr hptr.origin _ _ m) EvalExprlist.nil))) (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))))) (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'5 _ (Val.ofBool (!false)) (fun le m hp hT hH hag => EvalExpr.Ecast _ _ _ _ (EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _t'7 _ _ (hT.get (by temps_get))) (notbool_ofBool false m)) (cast_ofBool_bool _ m)))) ?_
              refine triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'5 _ (Val.ofBool (!false)) ?_
              intro le m hp hT hH hag
              exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _t'5 _ _ (hT.get (by temps_get))) (cast_ofBool_bool _ m)
            · refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), boolVal_ofBool_tint _ m⟩) ?_
              rw [if_pos rfl]
              exact return_const ge _ _ _ _ _ _ _ (Val.ofBool false) (fun _ => rfl)
                (fun hp hH => post_of c foundV word true false _ hp .reject (by simp [vdOf, matchNego, negInput, hw, hng, hcr]) rfl hH)
          · apply Sep.triple_seq_fwd
            · refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'19 _ (c.credsV) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_creds) rfl (H2_loads hpr hpn hptr hH hag).creds)) ?_
              refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ true _ _ _ (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), (boolVal_ptr_creds hptr (H2_loads hpr hpn hptr hH hag).valid).trans (by rw [hcr]; simp)⟩) ?_
              rw [if_pos rfl]
              refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'23 _ (c.credsV) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_creds) rfl (H2_loads hpr hpn hptr hH hag).creds)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'24 _ (.Vptr c.dataB c.dataO) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_data) rfl (H2_loads hpr hpn hptr hH hag).data)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'25 _ (c.scredsV) (fun le m hp hT hH hag => eval_state_field hcenv (hT.get (by temps_get)) off_screds rfl (H2_loads hpr hpn hptr hH hag).screds)) (call_fwd ge _ _ (credsSpec true) _t'6 _ _ emptyEnv _ emp (H2 c foundV word) emp (H2 c foundV word) (H2 c foundV word) [c.credsV, c.scredsV] (Val.ofBool true) bCs fdCs hCs hfCs htyCs rfl (fun _ _ _ => eval_callee_global rfl hsCs rfl) (fun le m hT => (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'23 _ (c.credsV) (hT.get (by temps_get))) (cast_ptr (creds_isPtr hptr) _ _ m) (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'25 _ (c.scredsV) (hT.get (by temps_get))) (cast_ptr hptr.screds _ _ m) EvalExprlist.nil))) (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))))) ?_
              refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (notbool_ofBool _ m), boolVal_ofBool_tint _ m⟩) ?_
              rw [if_neg Bool.false_ne_true]
              refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'20 _ (c.corigV) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_creds_origin) rfl (H2_loads hpr hpn hptr hH hag).corig)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'21 _ (.Vptr c.dataB c.dataO) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_data) rfl (H2_loads hpr hpn hptr hH hag).data)) (triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'22 _ (c.originV) (fun le m hp hT hH hag => eval_state_field hcenv (hT.get (by temps_get)) off_origin rfl (H2_loads hpr hpn hptr hH hag).origin)) (call_fwd ge _ _ (peerSpec true) _t'7 _ _ emptyEnv _ emp (H2 c foundV word) emp (H2 c foundV word) (H2 c foundV word) [c.corigV, c.originV] (Val.ofBool true) bPe fdPe hPe hfPe htyPe rfl (fun _ _ _ => eval_callee_global rfl hsPe rfl) (fun le m hT => (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'20 _ (c.corigV) (hT.get (by temps_get))) (cast_ptr hptr.corig _ _ m) (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'22 _ (c.originV) (hT.get (by temps_get))) (cast_ptr hptr.origin _ _ m) EvalExprlist.nil))) (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))))) (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'5 _ (Val.ofBool (!true)) (fun le m hp hT hH hag => EvalExpr.Ecast _ _ _ _ (EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _t'7 _ _ (hT.get (by temps_get))) (notbool_ofBool true m)) (cast_ofBool_bool _ m)))) ?_
              refine triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'5 _ (Val.ofBool (!true)) ?_
              intro le m hp hT hH hag
              exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _t'5 _ _ (hT.get (by temps_get))) (cast_ofBool_bool _ m)
            · refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), boolVal_ofBool_tint _ m⟩) ?_
              rw [if_neg Bool.false_ne_true]
              exact fall_to ge _ _ _ [(_m, .Vptr c.mB c.mO), (_conn, .Vptr c.connB c.connO)] _ _ _ (fun p hp => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl | rfl <;> temps_get)
                (by simp [vdOf, matchNego, negInput, hw, hng, hcr])
    case ttt =>
      refine triple_pure_pre ge _ _ _ _ _ _ (fun hφ => ?_)
      refine Sep.triple_seq ge _ _ _ Sep.Assn.no _ _ _ ?_ (triple_vacuous ge _ _ _ _)
      apply Sep.triple_seq_fwd
      · refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'15 _ (.Vint (Cop.bitfieldExtract .I32 .Unsigned 1 1 word)) (fun le m hp hT hH hag => eval_bitfield (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_want) (by decide) (by decide) (H2_loads hpr hpn hptr hH hag).word)) ?_
        refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), (boolVal_bit_val word 1 m).trans (by rw [hw])⟩) ?_
        rw [if_pos rfl]
        exact (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c foundV word) _t'10 _ (.Vint (Integers.Int.repr 1)) (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))
      · refine triple_if_local ge _ _ emptyEnv _ (H2 c foundV word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩) ?_
        rw [if_pos rfl]
        refine triple_seq_fwd ge _ _ _ _ _ _ _ (assign_found ge c foundV word _ hcenv hpw (by temps_get) (by temps_get)) ?_
        apply Sep.triple_seq_fwd
        · apply Sep.triple_seq_fwd
          · apply Sep.triple_seq_fwd
            · refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c (.Vptr c.connB c.connO) word) _t'13 _ (.Vint (Cop.bitfieldExtract .I32 .Unsigned 1 1 word)) (fun le m hp hT hH hag => eval_bitfield (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_want) (by decide) (by decide) (H2_loads hpr hpn hptr hH hag).word)) ?_
              refine triple_if_local ge _ _ emptyEnv _ (H2 c (.Vptr c.connB c.connO) word) _ true _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), (boolVal_bit_val word 1 m).trans (by rw [hw])⟩) ?_
              rw [if_pos rfl]
              refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c (.Vptr c.connB c.connO) word) _t'14 _ (.Vint c.ns) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_nego) rfl (H2_loads hpr hpn hptr hH hag).ns)) ?_
              refine triple_set_local_fwd ge _ _ emptyEnv _ (H2 c (.Vptr c.connB c.connO) word) _t'8 _ ((Val.ofBool (!Integers.Int.eq c.ns Integers.Int.zero))) ?_
              intro le m hp hT hH hag
              exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'14 _ _ (hT.get (by temps_get))) (EvalExpr.Econst_int _ _) (ne_zero_eval _ _ _)) (cast_ofBool_bool _ m)
            · refine triple_if_local ge _ _ emptyEnv _ (H2 c (.Vptr c.connB c.connO) word) _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), (boolVal_ofBool_tint _ m).trans (by rw [hng]; rfl)⟩) ?_
              rw [if_neg Bool.false_ne_true]
              refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ emptyEnv _ (H2 c (.Vptr c.connB c.connO) word) _t'11 _ (.Vint (Cop.bitfieldExtract .I32 .Unsigned 2 1 word)) (fun le m hp hT hH hag => eval_bitfield (hT.get (by temps_get)) (hcenv ▸ co_match) (hcenv ▸ off_proxy) (by decide) (by decide) (H2_loads hpr hpn hptr hH hag).word)) ?_
              refine triple_if_local ge _ _ emptyEnv _ (H2 c (.Vptr c.connB c.connO) word) _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), (boolVal_bit_val word 2 m).trans (by rw [hprox])⟩) ?_
              rw [if_neg Bool.false_ne_true]
              refine triple_set_local_fwd ge _ _ emptyEnv _ (H2 c (.Vptr c.connB c.connO) word) _t'9 _ (.Vint (Integers.Int.repr 0)) ?_
              intro le m hp hT hH hag
              exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl
          · refine triple_if_local ge _ _ emptyEnv _ (H2 c (.Vptr c.connB c.connO) word) _ false _ _ _ (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩) ?_
            rw [if_neg Bool.false_ne_true]
            exact triple_skip ge _ _ _
        · have hvd : vdOf c word cs oe = .candidate := by
            revert hφ; cases cs <;> cases oe <;> rcases hptr.creds with hcr | hcr <;> simp [vdOf, matchNego, negInput, hw, hng, hcr]
          exact return_const ge _ _ _ _ _ _ _ (Val.ofBool false) (fun _ => rfl)
            (fun hp hH => post_of c foundV word cs oe _ hp _ hvd rfl hH)


end Case2C
