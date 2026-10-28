/-
Case 2（CURL-CVE-2026-86413）: 修正後の `url_attach_existing`（curl 43029e2ec3、SPNEGO 有効・NTLM 無効・プロキシ無効）。

証明すること（`attach_after`）: この関数は、`Curl_cpool_find` の仕様 `findSpec (rawWant c && al)` のもとで
仕様 `attachSpec` を満たす。`findSpec` は前提に「渡す `match` の `want_nego_http` が `rawWant && allowed`、
`want_proxy_nego_http` が 0」を要求するので、これは呼び出しの時点でビットがそうなっていることを示す。
-/
import Case2Attach3
import Case5Config
import Case5Witness
open CC CC.Sep CC.HProp
open Case2_after
open Case5C (addr bitOf call_fwd sep_l sep_r cast_int_bool agrees_union triple_nop_loop eval_field
  boolVal_ofBool_tint)
open Case4C (IsPtr cast_ptr eval_deref_temp lv_field)

set_option maxRecDepth 20000

namespace Case2C

def attachSpec (c : Ctx3) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _connectdata noattr), tptr tbool]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp =>
    vargs = [.Vptr c.dataB c.dataO, .Vptr c.needleB c.needleO, .Vptr c.wpB c.wpO] ∧ ∃ wp, H3 c wp hp
  post := fun v hp => (∃ fb, v = Val.ofBool fb) ∧ ∃ wp, H3 c wp hp
  measure := fun _ => 0

theorem attach_entry_wf :
    listNorepet (varNames f_url_attach_existing.fn_vars)
    ∧ listNorepet (varNames f_url_attach_existing.fn_params)
    ∧ listDisjoint (varNames f_url_attach_existing.fn_params)
        (varNames f_url_attach_existing.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem lenz16 : (List.replicate 16 zeroByte).length = 16 := rfl

/-! ## 補助の規則 -/

theorem weaken_temps (ge fe f) {P : Sep.Assn} {s : Stmt} {E : Env} {l l' : List (Ident × Val)}
    {H : HProp} (h : Triple ge fe f P s (.only (LocalSt E l H))) (hsub : ∀ p ∈ l', p ∈ l) :
    Triple ge fe f P s (.only (LocalSt E l' H)) :=
  triple_conseq ge fe f h (fun _ _ _ x => x)
    (fun _ _ _ ⟨he, hT, hH⟩ => ⟨he, TempsHold_mono hsub hT, hH⟩)
    (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)

theorem pull_w (ge fe f) (E : Env) (l : List (Ident × Val)) (b : Block) (X : HProp) (s : Stmt)
    (R : Sep.ExitConds)
    (h : ∀ w, Triple ge fe f (LocalSt E l (MlocAny b w ∗ X)) s R) :
    Triple ge fe f (LocalSt E l ((fun hp => ∃ w, MlocAny b w hp) ∗ X)) s R := by
  intro k e le hp hf m hd hag ⟨he, hT, h1, h2, hd', heq, ⟨w, hw⟩, hx⟩
  exact h w k e le hp hf m hd hag ⟨he, hT, h1, h2, hd', heq, hw, hx⟩

/-- `PROTO_FAMILY_HTTP` の式の値。 -/
theorem eval_fam {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} :
    EvalExpr ge e le m
      (.Ebinop .Oor
        (.Ebinop .Oor
          (.Ebinop .Oor
            (.Ebinop .Oshl (.Econst_long (Integers.Int64.repr 1) tlong) (.Econst_int (Integers.Int.repr 0) tint) tlong)
            (.Ebinop .Oshl (.Econst_long (Integers.Int64.repr 1) tlong) (.Econst_int (Integers.Int.repr 1) tint) tlong)
            tlong)
          (.Ebinop .Oshl (.Econst_long (Integers.Int64.repr 1) tlong) (.Econst_int (Integers.Int.repr 30) tint) tlong)
          tlong)
        (.Ebinop .Oshl (.Ecast (.Econst_int (Integers.Int.repr 1) tint) tlong) (.Econst_int (Integers.Int.repr 31) tint) tlong)
        tlong)
      (.Vlong famC) :=
  EvalExpr.Ebinop _ _ _ _ _ _ _
    (EvalExpr.Ebinop _ _ _ _ _ _ _
      (EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_long _ _) (EvalExpr.Econst_int _ _) rfl)
        (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_long _ _) (EvalExpr.Econst_int _ _) rfl) rfl)
      (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_long _ _) (EvalExpr.Econst_int _ _) rfl) rfl)
    (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)
      (EvalExpr.Econst_int _ _) rfl) rfl

theorem blocks_envM {ge : CGenv} (hcenv : ge.genv_cenv = prog.prog_comp_env) (b : Block) :
    blocksOfEnv ge.genv_cenv (envM b) = [(b, 0, 48)] := by
  rw [hcenv]
  show (PTree.elements (PTree.set _match (b, tyM) PTree.empty)).map
         (blockOfBinding prog.prog_comp_env) = _
  rw [show PTree.elements (PTree.set _match (b, tyM) PTree.empty) = [(_match, (b, tyM))] from rfl]
  show [blockOfBinding prog.prog_comp_env (_match, (b, tyM))] = _
  rw [blockOfBinding, show tyM = Ty.Tstruct _url_conn_match noattr from rfl, sizeof_match]

set_option maxHeartbeats 4000000 in
theorem attach_after (ge : CGenv) (c : Ctx3) (mm al fb : Bool)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpw : permOrder c.pm .Writable = true)
    (hdest : IsPtr c.destV) (hcp : IsPtr c.cpV)
    (hnb : c.nowBytes.length = 16) (hnowal : Integers.Ptrofs.unsigned c.nowO % 8 = 0)
    (bInst bMs bNow bMm bPr bAl bFind bConn bRes : Block)
    (fdInst fdMs fdNow fdMm fdPr fdAl fdFind : FunDef)
    (hsInst : Genv.findSymbol ge.genv_genv _Curl_cpool_get_instance = some bInst)
    (hsMs : Genv.findSymbol ge.genv_genv _memset = some bMs)
    (hsNow : Genv.findSymbol ge.genv_genv _Curl_pgrs_now = some bNow)
    (hsMm : Genv.findSymbol ge.genv_genv _xfer_may_multiplex = some bMm)
    (hsPr : Genv.findSymbol ge.genv_genv _Curl_cpool_prune_dead = some bPr)
    (hsAl : Genv.findSymbol ge.genv_genv _Curl_auth_allowed_to_host = some bAl)
    (hsFind : Genv.findSymbol ge.genv_genv _Curl_cpool_find = some bFind)
    (hsConn : Genv.findSymbol ge.genv_genv _url_match_conn = some bConn)
    (hsRes : Genv.findSymbol ge.genv_genv _url_match_result = some bRes)
    (hfInst : FuncPtr ge bInst fdInst) (hfMs : FuncPtr ge bMs fdMs) (hfNow : FuncPtr ge bNow fdNow)
    (hfMm : FuncPtr ge bMm fdMm) (hfPr : FuncPtr ge bPr fdPr) (hfAl : FuncPtr ge bAl fdAl)
    (hfFind : FuncPtr ge bFind fdFind)
    (htyInst : typeOfFundef fdInst
      = .Tfunction (instSpec c.cpV).tyargs (instSpec c.cpV).tyres (instSpec c.cpV).cc)
    (htyMs : typeOfFundef fdMs = .Tfunction [tptr tvoid, tint, tulong] (tptr tvoid) cc_default)
    (htyNow : typeOfFundef fdNow = .Tfunction (nowSpec c).tyargs (nowSpec c).tyres (nowSpec c).cc)
    (htyMm : typeOfFundef fdMm = .Tfunction (mmSpec mm).tyargs (mmSpec mm).tyres (mmSpec mm).cc)
    (htyPr : typeOfFundef fdPr = .Tfunction pruneSpec.tyargs pruneSpec.tyres pruneSpec.cc)
    (htyAl : typeOfFundef fdAl
      = .Tfunction (allowSpec al).tyargs (allowSpec al).tyres (allowSpec al).cc)
    (htyFind : typeOfFundef fdFind
      = .Tfunction (findSpec true bFind fb).tyargs (findSpec true bFind fb).tyres cc_default)
    (hInst : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdInst (instSpec c.cpV) vs)
    (hMs : ∀ b vs, SatisfiesAt ge (FunctionEntry2 ge) fdMs (memsetSpec b) vs)
    (hNow : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdNow (nowSpec c) vs)
    (hMm : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdMm (mmSpec mm) vs)
    (hPr : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdPr pruneSpec vs)
    (hAl : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fdAl (allowSpec al) vs)
    (hFind : ∀ b vs, SatisfiesAt ge (FunctionEntry2 ge) fdFind (findSpec (rawWant c && al) b fb) vs)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_url_attach_existing) (attachSpec c) vs := by
  by_cases hvs : vs = [(.Vptr c.dataB c.dataO), (.Vptr c.needleB c.needleO), (.Vptr c.wpB c.wpO)]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := attach_entry_wf
  obtain ⟨rq, hrq⟩ : ∃ r, ∀ (ce : CompositeEnv) (m : Mem),
      Cop.semBinaryOperation ce .Oge (.Vint (Integers.Int.zero_ext 8 c.ussl)) tuchar
        (.Vlong (Integers.Int64.repr 2)) tlong m = some (Val.ofBool r) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨mt, hmt⟩ : ∃ r, ∀ (ce : CompositeEnv) (m : Mem),
      Cop.semBinaryOperation ce .Ogt (.Vint (Integers.Int.zero_ext 8 c.ussl)) tuchar
        (.Vlong (Integers.Int64.repr 0)) tlong m = some (Val.ofBool r) := ⟨_, fun _ _ => rfl⟩
  refine satisfies_internal ge (FunctionEntry2 ge) f_url_attach_existing _ _
    (fun e le hp => ∃ b wp, LocalSt (envM b) [(_waitpipe, (.Vptr c.wpB c.wpO)), (_needle, (.Vptr c.needleB c.needleO)), (_data, (.Vptr c.dataB c.dataO))] (H3 c wp ∗ undefBytes .Freeable b 0 48) e le hp)
    (fun m hp hf hpre hd hag => ?_) ?_
  · -- 入口: `match` を新しいブロックに確保する
    obtain ⟨_, wp, hH⟩ := hpre
    obtain ⟨hl, hu⟩ := undefBytes_exists .Freeable m.nextblock 0 48
    have hagp := Heap.Agrees_union_left hag
    have hagf := Heap.Agrees_union_right hd hag
    have hnone := fresh_none hag
    have hpn : ∀ o, hp m.nextblock o = none := fun o => by
      have := hnone o
      cases e : hp m.nextblock o with
      | none => rfl
      | some x => simp [Heap.union, e] at this
    have hfn : ∀ o, hf m.nextblock o = none := fun o => by
      have := hnone o
      simp only [Heap.union, hpn o] at this
      exact this
    have hdl : ∀ (h : Heap), (∀ o, h m.nextblock o = none) → Heap.disjoint h hl := by
      intro h hn b' o'
      by_cases hb : b' = m.nextblock
      · subst hb; exact Or.inl (hn o')
      · exact Or.inr (undefBytes_none hu b' o' (Or.inl hb))
    refine ⟨envM m.nextblock,
      PTree.set _waitpipe (.Vptr c.wpB c.wpO) (PTree.set _needle (.Vptr c.needleB c.needleO) (PTree.set _data (.Vptr c.dataB c.dataO)
        (createUndefTemps f_url_attach_existing.fn_temps))),
      (Mem.alloc m 0 48).1, hl, ?_, ?_, ?_, ?_⟩
    · refine FunctionEntry2.intro hnv hnp hdisj
        (AllocVariables.cons _ _ _ _ _ _ _ _ _ ?_ (AllocVariables.nil _ _)) rfl
      show Mem.alloc m 0 (sizeof ge.genv_cenv (Ty.Tstruct _url_conn_match noattr)) = _
      rw [hcenv, sizeof_match]
      exact Prod.ext rfl rfl
    · exact Heap.disjoint_union_left.mpr ⟨hd, Heap.disjoint_comm (hdl hf hfn)⟩
    · exact agrees_union (agrees_union (Heap.Agrees_alloc hagp) (undefBytes_agrees_alloc m 48 hu))
        (Heap.Agrees_alloc hagf)
    · refine ⟨m.nextblock, wp, rfl, TempsHold_cons (PTree.gss _ _ _) (TempsHold_cons ?_
        (TempsHold_cons ?_ (TempsHold_nil _))), hp, hl, hdl hp hpn, rfl, hH, hu⟩
      · exact (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)
      · exact (PTree.gso _ _ _ _ (by decide)).trans ((PTree.gso _ _ _ _ (by decide)).trans
          (PTree.gss _ _ _))
  -- 本体
  refine triple_exists ge _ _ (fun b e le hp => ∃ wp, LocalSt (envM b) [(_waitpipe, (.Vptr c.wpB c.wpO)), (_needle, (.Vptr c.needleB c.needleO)), (_data, (.Vptr c.dataB c.dataO))]
    (H3 c wp ∗ undefBytes .Freeable b 0 48) e le hp) _ _ (fun b => ?_)
  refine triple_exists ge _ _ (fun wp => LocalSt (envM b) [(_waitpipe, (.Vptr c.wpB c.wpO)), (_needle, (.Vptr c.needleB c.needleO)), (_data, (.Vptr c.dataB c.dataO))]
    (H3 c wp ∗ undefBytes .Freeable b 0 48)) _ _ (fun wp => ?_)
  -- S1: cpool = Curl_cpool_get_instance(data);
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (call_fwd ge _ _ (instSpec c.cpV) _t'1 _ _ (envM b) _ emp (H3 c wp ∗ undefBytes .Freeable b 0 48)
        emp _ _ [(.Vptr c.dataB c.dataO)] c.cpV bInst fdInst hInst hfInst htyInst rfl (fun _ _ _ => eval_callee_global (envM_none b _ (by decide)) hsInst rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _data _ (.Vptr c.dataB c.dataO) (hT.get (by temps_get))) rfl EvalExprlist.nil)
        (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))
      (triple_set_local_fwd ge _ _ (envM b) _ _ _cpool__1 _ c.cpV
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))) ?_
  -- S2: DEBUGASSERT
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_nop_loop ge _ _ _) ?_
  -- S3: memset(&match, 0, sizeof(match));
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_rw ge _ _ (envM b) _ _ (H3 c wp ∗ undefBytes .Freeable b 0 48)
      (undefBytes .Freeable b 0 48 ∗ H3 c wp)
      (H3 c wp ∗ bytesPtsTo b .Freeable 0 (List.replicate 48 zeroByte))
      (bytesPtsTo b .Freeable 0 (List.replicate 48 zeroByte) ∗ H3 c wp) _
      (sep_comm_eq _ _) (sep_comm_eq _ _)
      (call_void ge _ _ (memsetSpec b) _ _ (envM b) _ _ _ _
        [.Vptr b Integers.Ptrofs.zero, .Vint (Integers.Int.repr 0), Val.Vptrofs (Integers.Ptrofs.repr 48)]
        bMs fdMs (hMs b) hfMs htyMs rfl (fun _ _ _ => eval_callee_global (envM_none b _ (by decide)) hsMs rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Eaddrof _ _ b Integers.Ptrofs.zero (EvalLvalue.Evar_local _ b _ (envM_get b))) rfl
          (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl
            (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Esizeof _ _) (by rw [hcenv, sizeof_match]; rfl)
              EvalExprlist.nil)))
        (fun _ hu => ⟨rfl, hu⟩) (fun _ _ hp => hp))) ?_
  rw [zeros_Mloc]
  -- S4: match.data = data;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_rw ge _ _ (envM b) _ _ _ _ _ _ _ (pick8 (H3 c wp) b (.Vlong (Integers.Int64.repr 0)) (.Vlong (Integers.Int64.repr 0)) (.Vlong (Integers.Int64.repr 0)) (List.replicate 16 zeroByte) (Integers.Int.repr 0) (List.replicate 4 zeroByte))
      (pick8 (H3 c wp) b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vlong (Integers.Int64.repr 0)) (List.replicate 16 zeroByte) (Integers.Int.repr 0) (List.replicate 4 zeroByte))
      (assign_head ge _ _ (envM b) _ _ _ _ Mptr .Freeable b
        (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 8)) 8 (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) rfl rfl uz8
        (fun le m _ => lv_match_field hcenv off_mdata)
        (fun le m hT => ⟨_, (EvalExpr.Etempvar _data _ (.Vptr c.dataB c.dataO) (hT.get (by temps_get))), rfl⟩))) ?_
  -- S5: match.needle = needle;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_rw ge _ _ (envM b) _ _ _ _ _ _ _ (pick16 (H3 c wp) b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vlong (Integers.Int64.repr 0)) (List.replicate 16 zeroByte) (Integers.Int.repr 0) (List.replicate 4 zeroByte))
      (pick16 (H3 c wp) b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) (List.replicate 16 zeroByte) (Integers.Int.repr 0) (List.replicate 4 zeroByte))
      (assign_head ge _ _ (envM b) _ _ _ _ Mptr .Freeable b
        (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 16)) 16 (.Vlong (Integers.Int64.repr 0)) (.Vptr c.needleB c.needleO) rfl rfl uz16
        (fun le m _ => lv_match_field hcenv off_mneedle)
        (fun le m hT => ⟨_, EvalExpr.Etempvar _needle _ (.Vptr c.needleB c.needleO) (hT.get (by temps_get)), rfl⟩))) ?_
  -- S6: match.now = *Curl_pgrs_now(data);
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (call_fwd ge _ _ (nowSpec c) _t'2 _ _ (envM b) _ emp (H3 c wp ∗ (Mloc b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) (List.replicate 16 zeroByte) (Integers.Int.repr 0) (List.replicate 4 zeroByte)))
        emp _ _ [(.Vptr c.dataB c.dataO)] (.Vptr c.nowB c.nowO) bNow fdNow hNow hfNow htyNow rfl (fun _ _ _ => eval_callee_global (envM_none b _ (by decide)) hsNow rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _data _ (.Vptr c.dataB c.dataO) (hT.get (by temps_get))) rfl EvalExprlist.nil)
        (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))
      (triple_rw ge _ _ (envM b) _ _ _ _ _ _ _
        (picknow c wp b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) (List.replicate 16 zeroByte) (Integers.Int.repr 0) (List.replicate 4 zeroByte))
        (picknow c wp b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (Integers.Int.repr 0) (List.replicate 4 zeroByte))
        (triple_assign_copy ge _ _ _ _ _ _ c.pm .Freeable c.nowB c.nowO b
          (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 24)) c.nowBytes (List.replicate 16 zeroByte) hpr rfl rfl
          (show ((c.nowBytes.length : Nat) : _root_.Int)
              = sizeof ge.genv_cenv (Ty.Tstruct _curltime noattr) by rw [hnb, hcenv]; decide)
          (by rw [hnb]; rfl)
          (fun _ => show Integers.Ptrofs.unsigned c.nowO
              % alignofBlockcopy ge.genv_cenv (Ty.Tstruct _curltime noattr) = 0 by
            rw [hcenv, show alignofBlockcopy prog.prog_comp_env (Ty.Tstruct _curltime noattr) = 8
              from by decide]; exact hnowal)
          (fun _ => show Integers.Ptrofs.unsigned
              (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 24))
              % alignofBlockcopy ge.genv_cenv (Ty.Tstruct _curltime noattr) = 0 by
            rw [hcenv, show alignofBlockcopy prog.prog_comp_env (Ty.Tstruct _curltime noattr) = 8
              from by decide, uz24]; decide)
          (fun e le hp m hP _ => by
            obtain ⟨he, hT, hD, hX, hdDX, rfl, hnow, hS, hR, hdSR, rfl, hsrc, hrest⟩ := hP
            subst he
            refine ⟨hS, hD, hR, hdSR, hdDX, rfl, hsrc, (by rw [uz24]; exact hnow),
              lv_match_field hcenv off_now,
              EvalExpr.Elvalue _ _ _ .Full _
                (EvalLvalue.Ederef _ _ _ _ (EvalExpr.Etempvar _t'2 _ _ (hT.get (by temps_get))))
                (DerefLoc.copy rfl),
              semCast_struct_same _ _ _ _ _ _, fun hD' hnow' hd' => ?_⟩
            exact ⟨rfl, hT, hD', Heap.union hS hR, hd', rfl, (by rw [uz24] at hnow'; exact hnow'),
              hS, hR, hdSR, rfl, hsrc, hrest⟩)))) ?_
  -- S7: match.may_multiplex = xfer_may_multiplex(data, needle);
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (call_fwd ge _ _ (mmSpec mm) _t'3 _ _ (envM b) _ emp (H3 c wp ∗ (Mloc b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (Integers.Int.repr 0) (List.replicate 4 zeroByte)))
        emp _ _ [(.Vptr c.dataB c.dataO), (.Vptr c.needleB c.needleO)] (Val.ofBool mm) bMm fdMm hMm hfMm htyMm rfl (fun _ _ _ => eval_callee_global (envM_none b _ (by decide)) hsMm rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _data _ (.Vptr c.dataB c.dataO) (hT.get (by temps_get))) rfl
          (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _needle _ (.Vptr c.needleB c.needleO) (hT.get (by temps_get))) rfl
            EvalExprlist.nil))
        (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _))
      (triple_rw ge _ _ (envM b) _ _ _ _ _ _ _
        (pickw (H3 c wp) b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (Integers.Int.repr 0) (List.replicate 4 zeroByte))
        (pickw (H3 c wp) b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 0 (Integers.Int.repr 0) (boolInt mm)) (List.replicate 4 zeroByte))
        (assign_bits_head ge _ _ (envM b) _ _ _ _ b
          (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 40)) 40 0
          (Integers.Int.repr 0) (boolInt mm) rfl (by decide) (by decide) uz40
          (fun le m _ => lv_match_field hcenv off_mm)
          (fun le m hT => ⟨_, EvalExpr.Etempvar _t'3 _ (Val.ofBool mm) (hT.get (by temps_get)),
            cast_ofBool_bool_int mm m⟩)))) ?_
  -- S8: Curl_cpool_prune_dead(cpool, data);
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_rw ge _ _ (envM b) _ _ _ _ _ _ _ (emp_sep_eq _).symm (emp_sep_eq _).symm
      (call_void ge _ _ pruneSpec _ _ (envM b) _ emp emp _ [c.cpV, (.Vptr c.dataB c.dataO)] bPr fdPr hPr hfPr htyPr rfl
        (fun _ _ _ => eval_callee_global (envM_none b _ (by decide)) hsPr rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _cpool__1 _ c.cpV (hT.get (by temps_get))) (cast_ptr hcp _ _ m)
          (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _data _ (.Vptr c.dataB c.dataO) (hT.get (by temps_get))) rfl EvalExprlist.nil))
        (fun _ he => he) (fun _ _ hp => hp))) ?_
  -- S9: match.want_nego_http = (want & NEGOTIATE) && (protocol & FAMILY_HTTP) && Curl_auth_allowed_to_host(data);
  refine triple_seq_fwd ge _ _ _ (LocalSt (envM b) [(_waitpipe, (.Vptr c.wpB c.wpO)), (_needle, (.Vptr c.needleB c.needleO)), (_data, (.Vptr c.dataB c.dataO))] (H3 c wp ∗ (Mloc b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt (rawWant c && al))) (List.replicate 4 zeroByte)))) _ _ _ ?s9 ?rest
  case s9 =>
    cases h1 : rw1 c
    · apply weaken_temps
      · apply Sep.triple_seq_fwd
        · apply Sep.triple_seq_fwd
          · refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ (envM b) _ (H3 c wp ∗ (Mloc b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 0 (Integers.Int.repr 0) (boolInt mm)) (List.replicate 4 zeroByte))) _t'12 _ (.Vint c.want32) (fun le m hp hT hH hag => EvalExpr.Elvalue _ _ _ .Full _ (lv_field (EvalExpr.Elvalue _ _ _ .Full _ (lv_field (EvalExpr.Elvalue _ _ _ .Full _ (lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_easy) (hcenv ▸ off_state)) (DerefLoc.copy rfl)) rfl (hcenv ▸ co_state) (hcenv ▸ off_authhost)) (DerefLoc.copy rfl)) rfl (hcenv ▸ co_auth) (hcenv ▸ off_want32)) (DerefLoc.value .Mint32 _ rfl (H3_loads hpr hdest hH hag).want))) ?_
            refine triple_if_local ge _ _ (envM b) _ _ _ false _ _ _
              (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'12 _ _ (hT.get (by temps_get))) (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl) (EvalExpr.Econst_int _ _) rfl) rfl, (show Cop.boolVal _ tulong m = some (rw1 c) from rfl).trans (by rw [h1])⟩) ?_
            rw [if_neg Bool.false_ne_true]
            exact triple_set_local_fwd ge _ _ (envM b) _ _ _t'4 _ (.Vint (Integers.Int.repr 0))
              (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)
          · refine triple_if_local ge _ _ (envM b) _ _ _ false _ _ _
              (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), rfl⟩) ?_
            rw [if_neg Bool.false_ne_true]
            exact triple_set_local_fwd ge _ _ (envM b) _ _ _t'5 _ (.Vint (Integers.Int.repr 0))
              (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)
        · exact (triple_rw ge _ _ (envM b) _ _ _ _ _ _ _ (pickw (H3 c wp) b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 0 (Integers.Int.repr 0) (boolInt mm)) (List.replicate 4 zeroByte)) (pickw (H3 c wp) b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt (rawWant c && al))) (List.replicate 4 zeroByte)) (assign_bits_head ge _ _ (envM b) _ _ _ _ b (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 40)) 40 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt (rawWant c && al)) rfl (by decide) (by decide) uz40 (fun le m _ => lv_match_field hcenv off_want) (fun le m hT => ⟨_, EvalExpr.Etempvar _t'5 _ _ (hT.get (by temps_get)), by rw [show rawWant c = false from by simp [rawWant, h1]]; rfl⟩)))
      · exact (fun p hp => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl | rfl | rfl <;> temps_get)
    · cases h2 : rw2 c
      · apply weaken_temps
        · apply Sep.triple_seq_fwd
          · apply Sep.triple_seq_fwd
            · refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ (envM b) _ (H3 c wp ∗ (Mloc b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 0 (Integers.Int.repr 0) (boolInt mm)) (List.replicate 4 zeroByte))) _t'12 _ (.Vint c.want32) (fun le m hp hT hH hag => EvalExpr.Elvalue _ _ _ .Full _ (lv_field (EvalExpr.Elvalue _ _ _ .Full _ (lv_field (EvalExpr.Elvalue _ _ _ .Full _ (lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_easy) (hcenv ▸ off_state)) (DerefLoc.copy rfl)) rfl (hcenv ▸ co_state) (hcenv ▸ off_authhost)) (DerefLoc.copy rfl)) rfl (hcenv ▸ co_auth) (hcenv ▸ off_want32)) (DerefLoc.value .Mint32 _ rfl (H3_loads hpr hdest hH hag).want))) ?_
              refine triple_if_local ge _ _ (envM b) _ _ _ true _ _ _
                (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'12 _ _ (hT.get (by temps_get))) (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl) (EvalExpr.Econst_int _ _) rfl) rfl, (show Cop.boolVal _ tulong m = some (rw1 c) from rfl).trans (by rw [h1])⟩) ?_
              rw [if_pos rfl]
              refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ (envM b) _ (H3 c wp ∗ (Mloc b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 0 (Integers.Int.repr 0) (boolInt mm)) (List.replicate 4 zeroByte))) _t'13 _ (.Vptr c.schemeB c.schemeO) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_scheme2) rfl (H3_loads hpr hdest hH hag).scheme)) ?_
              refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ (envM b) _ (H3 c wp ∗ (Mloc b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 0 (Integers.Int.repr 0) (boolInt mm)) (List.replicate 4 zeroByte))) _t'14 _ (.Vlong c.proto) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_scheme2) (hcenv ▸ off_protocol2) rfl (H3_loads hpr hdest hH hag).proto)) ?_
              refine triple_set_local_fwd ge _ _ (envM b) _ _ _t'4 _ (Val.ofBool (rw2 c)) ?_
              intro le m hp hT hH hag
              exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _
                (EvalExpr.Etempvar _t'14 _ _ (hT.get (by temps_get))) eval_fam rfl) (cast_long_bool _ m)
            · refine triple_if_local ge _ _ (envM b) _ _ _ false _ _ _
                (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
                  (boolVal_ofBool_tint _ m).trans (by rw [h2])⟩) ?_
              rw [if_neg Bool.false_ne_true]
              exact triple_set_local_fwd ge _ _ (envM b) _ _ _t'5 _ (.Vint (Integers.Int.repr 0))
                (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)
          · exact (triple_rw ge _ _ (envM b) _ _ _ _ _ _ _ (pickw (H3 c wp) b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 0 (Integers.Int.repr 0) (boolInt mm)) (List.replicate 4 zeroByte)) (pickw (H3 c wp) b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt (rawWant c && al))) (List.replicate 4 zeroByte)) (assign_bits_head ge _ _ (envM b) _ _ _ _ b (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 40)) 40 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt (rawWant c && al)) rfl (by decide) (by decide) uz40 (fun le m _ => lv_match_field hcenv off_want) (fun le m hT => ⟨_, EvalExpr.Etempvar _t'5 _ _ (hT.get (by temps_get)), by rw [show rawWant c = false from by simp [rawWant, h1, h2]]; rfl⟩)))
        · exact (fun p hp => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl | rfl | rfl <;> temps_get)
      · apply weaken_temps
        · apply Sep.triple_seq_fwd
          · apply Sep.triple_seq_fwd
            · refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ (envM b) _ (H3 c wp ∗ (Mloc b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 0 (Integers.Int.repr 0) (boolInt mm)) (List.replicate 4 zeroByte))) _t'12 _ (.Vint c.want32) (fun le m hp hT hH hag => EvalExpr.Elvalue _ _ _ .Full _ (lv_field (EvalExpr.Elvalue _ _ _ .Full _ (lv_field (EvalExpr.Elvalue _ _ _ .Full _ (lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_easy) (hcenv ▸ off_state)) (DerefLoc.copy rfl)) rfl (hcenv ▸ co_state) (hcenv ▸ off_authhost)) (DerefLoc.copy rfl)) rfl (hcenv ▸ co_auth) (hcenv ▸ off_want32)) (DerefLoc.value .Mint32 _ rfl (H3_loads hpr hdest hH hag).want))) ?_
              refine triple_if_local ge _ _ (envM b) _ _ _ true _ _ _
                (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'12 _ _ (hT.get (by temps_get))) (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl) (EvalExpr.Econst_int _ _) rfl) rfl, (show Cop.boolVal _ tulong m = some (rw1 c) from rfl).trans (by rw [h1])⟩) ?_
              rw [if_pos rfl]
              refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ (envM b) _ (H3 c wp ∗ (Mloc b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 0 (Integers.Int.repr 0) (boolInt mm)) (List.replicate 4 zeroByte))) _t'13 _ (.Vptr c.schemeB c.schemeO) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_scheme2) rfl (H3_loads hpr hdest hH hag).scheme)) ?_
              refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_set_local_fwd ge _ _ (envM b) _ (H3 c wp ∗ (Mloc b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 0 (Integers.Int.repr 0) (boolInt mm)) (List.replicate 4 zeroByte))) _t'14 _ (.Vlong c.proto) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_scheme2) (hcenv ▸ off_protocol2) rfl (H3_loads hpr hdest hH hag).proto)) ?_
              refine triple_set_local_fwd ge _ _ (envM b) _ _ _t'4 _ (Val.ofBool (rw2 c)) ?_
              intro le m hp hT hH hag
              exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _
                (EvalExpr.Etempvar _t'14 _ _ (hT.get (by temps_get))) eval_fam rfl) (cast_long_bool _ m)
            · refine triple_if_local ge _ _ (envM b) _ _ _ true _ _ _
                (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)),
                  (boolVal_ofBool_tint _ m).trans (by rw [h2])⟩) ?_
              rw [if_pos rfl]
              refine triple_seq_fwd ge _ _ _ _ _ _ _
                (call_fwd ge _ _ (allowSpec al) _t'6 _ _ (envM b) _ emp (H3 c wp ∗ (Mloc b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 0 (Integers.Int.repr 0) (boolInt mm)) (List.replicate 4 zeroByte))) emp _ _ [(.Vptr c.dataB c.dataO)] (Val.ofBool al)
                  bAl fdAl hAl hfAl htyAl rfl (fun _ _ _ => eval_callee_global (envM_none b _ (by decide)) hsAl rfl)
                  (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _data _ (.Vptr c.dataB c.dataO) (hT.get (by temps_get))) rfl EvalExprlist.nil)
                  (fun _ he => he) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _)) ?_
              refine triple_set_local_fwd ge _ _ (envM b) _ _ _t'5 _ (Val.ofBool al) ?_
              intro le m hp hT hH hag
              exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _t'6 _ _ (hT.get (by temps_get)))
                (cast_ofBool_bb al m)
          · exact (triple_rw ge _ _ (envM b) _ _ _ _ _ _ _ (pickw (H3 c wp) b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 0 (Integers.Int.repr 0) (boolInt mm)) (List.replicate 4 zeroByte)) (pickw (H3 c wp) b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt (rawWant c && al))) (List.replicate 4 zeroByte)) (assign_bits_head ge _ _ (envM b) _ _ _ _ b (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 40)) 40 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt (rawWant c && al)) rfl (by decide) (by decide) uz40 (fun le m _ => lv_match_field hcenv off_want) (fun le m hT => ⟨_, EvalExpr.Etempvar _t'5 _ _ (hT.get (by temps_get)), by rw [show rawWant c = true from by simp [rawWant, h1, h2], Bool.true_and]; exact cast_ofBool_int al m⟩)))
        · exact (fun p hp => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp; rcases hp with rfl | rfl | rfl <;> temps_get)
  case rest =>
  -- S10: match.require_tls = data->set.use_ssl >= CURLUSESSL_CONTROL;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envM b) _ (H3 c wp ∗ (Mloc b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt (rawWant c && al))) (List.replicate 4 zeroByte))) _t'11 _ (.Vint (Integers.Int.zero_ext 8 c.ussl)) (fun le m hp hT hH hag => EvalExpr.Elvalue _ _ _ .Full _ (lv_field (EvalExpr.Elvalue _ _ _ .Full _ (lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_easy) (hcenv ▸ off_set2)) (DerefLoc.copy rfl)) rfl (hcenv ▸ co_ud) (hcenv ▸ off_use_ssl)) (DerefLoc.value .Mint8unsigned _ rfl (H3_loads hpr hdest hH hag).ussl)))
      (triple_rw ge _ _ (envM b) _ _ _ _ _ _ _
        (pickw (H3 c wp) b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt (rawWant c && al))) (List.replicate 4 zeroByte))
        (pickw (H3 c wp) b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 4 (ins 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt (rawWant c && al))) (boolInt rq)) (List.replicate 4 zeroByte))
        (assign_bits_head ge _ _ (envM b) _ _ _ _ b
          (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 40)) 40 4 (ins 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt (rawWant c && al))) (boolInt rq)
          rfl (by decide) (by decide) uz40
          (fun le m _ => lv_match_field hcenv off_reqtls)
          (fun le m hT => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
            (EvalExpr.Etempvar _t'11 _ _ (hT.get (by temps_get))) (EvalExpr.Econst_long _ _) (hrq _ _),
            cast_ofBool_int rq m⟩)))) ?_
  -- S11: match.may_tls = data->set.use_ssl > CURLUSESSL_NONE;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envM b) _ (H3 c wp ∗ (Mloc b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 4 (ins 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt (rawWant c && al))) (boolInt rq)) (List.replicate 4 zeroByte))) _t'10 _ (.Vint (Integers.Int.zero_ext 8 c.ussl)) (fun le m hp hT hH hag => EvalExpr.Elvalue _ _ _ .Full _ (lv_field (EvalExpr.Elvalue _ _ _ .Full _ (lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_easy) (hcenv ▸ off_set2)) (DerefLoc.copy rfl)) rfl (hcenv ▸ co_ud) (hcenv ▸ off_use_ssl)) (DerefLoc.value .Mint8unsigned _ rfl (H3_loads hpr hdest hH hag).ussl)))
      (triple_rw ge _ _ (envM b) _ _ _ _ _ _ _
        (pickw (H3 c wp) b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 4 (ins 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt (rawWant c && al))) (boolInt rq)) (List.replicate 4 zeroByte))
        (pickw (H3 c wp) b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 3 (ins 4 (ins 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt (rawWant c && al))) (boolInt rq)) (boolInt mt)) (List.replicate 4 zeroByte))
        (assign_bits_head ge _ _ (envM b) _ _ _ _ b
          (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 40)) 40 3 (ins 4 (ins 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt (rawWant c && al))) (boolInt rq)) (boolInt mt)
          rfl (by decide) (by decide) uz40
          (fun le m _ => lv_match_field hcenv off_maytls)
          (fun le m hT => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
            (EvalExpr.Etempvar _t'10 _ _ (hT.get (by temps_get))) (EvalExpr.Econst_long _ _) (hmt _ _),
            cast_ofBool_int mt m⟩)))) ?_
  -- S12: success = Curl_cpool_find(data, needle->destination, url_match_conn, url_match_result, &match);
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ (envM b) _ (H3 c wp ∗ (Mloc b (.Vlong (Integers.Int64.repr 0)) (.Vptr c.dataB c.dataO) (.Vptr c.needleB c.needleO) c.nowBytes (ins 3 (ins 4 (ins 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt (rawWant c && al))) (boolInt rq)) (boolInt mt)) (List.replicate 4 zeroByte))) _t'9 _ (c.destV) (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_conn) (hcenv ▸ off_destination) rfl (H3_loads hpr hdest hH hag).dest))
        (triple_pre ge _ _ (P := LocalSt (envM b) _ (MlocAny b (ins 3 (ins 4 (ins 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt (rawWant c && al))) (boolInt rq)) (boolInt mt)) ∗ H3 c wp))
          (fun e le hp ⟨he, hT, h1, h2, hd, heq, hh3, hml⟩ =>
            ⟨he, hT, h2, h1, Heap.disjoint_comm hd, heq.trans (Heap.union_comm hd),
             Mloc_any hnb rfl hml, hh3⟩)
          (call_fwd ge _ _ (findSpec (rawWant c && al) b fb) _t'7 _ _ (envM b) _ (MlocAny b (ins 3 (ins 4 (ins 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt (rawWant c && al))) (boolInt rq)) (boolInt mt)))
            (H3 c wp) (fun hp => ∃ w, MlocAny b w hp) _ _
            [(.Vptr c.dataB c.dataO), c.destV, .Vptr bConn Integers.Ptrofs.zero, .Vptr bRes Integers.Ptrofs.zero,
             .Vptr b Integers.Ptrofs.zero]
            (Val.ofBool fb) bFind fdFind (hFind b) hfFind htyFind rfl (fun _ _ _ => eval_callee_global (envM_none b _ (by decide)) hsFind rfl)
            (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _data _ (.Vptr c.dataB c.dataO) (hT.get (by temps_get))) rfl
              (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _t'9 _ c.destV (hT.get (by temps_get)))
                (cast_ptr hdest _ _ m)
                (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Elvalue _ bConn Integers.Ptrofs.zero .Full _
                    (EvalLvalue.Evar_global _ bConn _ (envM_none b _ (by decide)) hsConn)
                    (DerefLoc.reference rfl)) rfl
                  (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Elvalue _ bRes Integers.Ptrofs.zero .Full _
                      (EvalLvalue.Evar_global _ bRes _ (envM_none b _ (by decide)) hsRes)
                      (DerefLoc.reference rfl)) rfl
                    (EvalExprlist.cons _ _ _ _ _ _ _
                      (EvalExpr.Eaddrof _ _ b Integers.Ptrofs.zero (EvalLvalue.Evar_local _ b _ (envM_get b)))
                      rfl EvalExprlist.nil)))))
            (fun _ hh => ⟨⟨_, _, _, _, rfl⟩, (ins 3 (ins 4 (ins 1 (ins 0 (Integers.Int.repr 0) (boolInt mm)) (boolInt (rawWant c && al))) (boolInt rq)) (boolInt mt)), (bits_after mm (rawWant c && al) rq mt).1,
              (bits_after mm (rawWant c && al) rq mt).2, hh⟩)
            (fun _ _ hp => hp) rfl rfl)))
      (triple_set_local_fwd ge _ _ (envM b) _ _ _success _ (Val.ofBool fb)
        (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
          (EvalExpr.Etempvar _t'7 _ _ (hT.get (by temps_get))) (cast_ofBool_bb fb m)))) ?_
  -- S13・S14
  refine pull_w ge _ _ (envM b) _ b (H3 c wp) _ _ (fun w' => ?_)
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envM b) _ (MlocAny b w' ∗ H3 c wp) _t'8 _
        (.Vint (Cop.bitfieldExtract .I32 .Unsigned 5 1 w'))
        (fun le m hp hT hH hag => eval_match_bits hcenv off_waitpipe (by decide) (by decide)
          (mlocAny_load hH hag)))
      (triple_rw ge _ _ (envM b) _ _ _ _ _ _ _ (pickwp c wp (MlocAny b w'))
        (pickwp c (Val.ofBool (bitOf w' 5)) (MlocAny b w'))
        (assign_head ge _ _ (envM b) _ _ _ _ .Mbool c.pm c.wpB c.wpO
          (Integers.Ptrofs.unsigned c.wpO) wp (Val.ofBool (bitOf w' 5)) hpw rfl rfl
          (fun le m hT => EvalLvalue.Ederef _ _ _ _
            (EvalExpr.Etempvar _waitpipe _ (.Vptr c.wpB c.wpO) (hT.get (by temps_get))))
          (fun le m hT => ⟨_, EvalExpr.Ecast _ _ _ _
            (EvalExpr.Etempvar _t'8 _ _ (hT.get (by temps_get))) (cast_int_bool _ m),
            cast_ofBool_bb _ m⟩)))) ?_
  -- return success;
  refine triple_return ge _ _ _ _ _ (fun e le hp m hP hag => ?_)
  obtain ⟨he, hT, hL, hH3, hdLH, rfl, hml, hh3⟩ := hP
  subst he
  have hrp := mlocAny_rangePerm hml (Heap.Agrees_union_left hag)
  obtain ⟨m', hm'⟩ := freeList_isSome_of_rangePerm [(b, 0, 48)] m
    (fun blk hb => by simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb; subst hb; exact hrp)
    (by simp)
  refine ⟨Val.ofBool fb, Val.ofBool fb, m', hH3,
    EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)), cast_ofBool_bb fb m,
    (by rw [blocks_envM hcenv b]; exact hm'), ⟨⟨fb, rfl⟩, _, hh3⟩, fun hf hd hag' => ?_⟩
  have hd' := Heap.disjoint_union_left.mp hd
  refine ⟨hd'.2, Sep.Agrees_freeList [(b, 0, 48)] m m' hm' ?_ (agrees_drop hdLH hd'.1 hag')⟩
  intro blk hb ofs h0 h48
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
  subst hb
  have hown := mlocAny_owns hml ofs h0 h48
  have e3 : hH3 b ofs = none := (hdLH b ofs).resolve_left hown
  have ef : hf b ofs = none := (hd'.1 b ofs).resolve_left hown
  simp [Heap.union, e3, ef]

end Case2C
