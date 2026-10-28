/-
Case 1 の P1: 修正後の `Curl_pp_readresp` は、呼ばれる側の関数がどう振る舞っても（仕様の範囲で）return に達する。

- `pingpong_read` は翻訳単位の中の関数なので、仕様（`recvSpec`）を本体から導く（`pread_ok`）
- 関数の本体は、局所変数 gotbytes・buffer を確保したあとの環境 `envE` から始める（入口は含めない）
- 三つ組は全正当性（return に達する実行がある）。0 バイトの経路は `recvSpec` の前提で除いている（Case1Spec）
-/
import Case1Outer
open CC CC.Sep CC.HProp
open Case1_after
open Case5C (addr eval_field boolVal_ofBool_tint boolVal_ofBool_tbool)
open Case4C (IsPtr cast_ptr lv_field eval_deref_temp loadResult_ptr)

set_option maxRecDepth 20000

namespace Case1C

variable {ge : CGenv} {c : Ctx} {DB : Nat → Val → HProp}

/-! ## `pingpong_read` -/

theorem pread_entry_wf :
    listNorepet (varNames f_pingpong_read.fn_vars)
    ∧ listNorepet (varNames f_pingpong_read.fn_params)
    ∧ listDisjoint (varNames f_pingpong_read.fn_params) (varNames f_pingpong_read.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

abbrev lR (c : Ctx) : List (Ident × Val) :=
  [(_nread, .Vptr c.bg Integers.Ptrofs.zero), (_buflen, v900),
   (_buffer, .Vptr c.bb Integers.Ptrofs.zero), (_sockindex, c.sockV),
   (_data, .Vptr c.dataB c.dataO)]

/-- `pingpong_read` は `Curl_conn_recv` を呼んで、その結果を返すだけ。仕様も同じになる。 -/
theorem pread_ok (X : Ext c DB ge) :
    ∀ n p gv vs, SatisfiesAt ge (FunctionEntry2 ge) X.pread.fd (recvSpec c DB n p gv) vs := by
  intro n p gv vs
  rw [X.pread_fd]
  by_cases hvs : vs = [.Vptr c.dataB c.dataO, c.sockV, .Vptr c.bb Integers.Ptrofs.zero, v900,
    .Vptr c.bg Integers.Ptrofs.zero]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := pread_entry_wf
  refine satisfies_internal_noVars ge (FunctionEntry2 ge) f_pingpong_read _ _
    (LocalSt emptyEnv (lR c) (H c DB n p gv)) (fun m => ?_) ?_
  · refine ⟨PTree.set _nread (.Vptr c.bg Integers.Ptrofs.zero)
              (PTree.set _buflen v900
                (PTree.set _buffer (.Vptr c.bb Integers.Ptrofs.zero)
                  (PTree.set _sockindex c.sockV
                    (PTree.set _data (.Vptr c.dataB c.dataO)
                      (createUndefTemps f_pingpong_read.fn_temps))))),
            FunctionEntry2.intro hnv hnp hdisj (AllocVariables.nil _ _) rfl,
            fun hp hpre => ⟨rfl, ?_, hpre.2⟩⟩
    refine TempsHold_cons (PTree.gss _ _ _) (TempsHold_cons ?_ (TempsHold_cons ?_
      (TempsHold_cons ?_ (TempsHold_cons ?_ (TempsHold_nil _)))))
    · exact (PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)
    · exact (PTree.gso _ _ _ _ (by decide)).trans ((PTree.gso _ _ _ _ (by decide)).trans
        (PTree.gss _ _ _))
    · exact (PTree.gso _ _ _ _ (by decide)).trans ((PTree.gso _ _ _ _ (by decide)).trans
        ((PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _)))
    · exact (PTree.gso _ _ _ _ (by decide)).trans ((PTree.gso _ _ _ _ (by decide)).trans
        ((PTree.gso _ _ _ _ (by decide)).trans ((PTree.gso _ _ _ _ (by decide)).trans
          (PTree.gss _ _ _))))
  -- t'1 = Curl_conn_recv(data, sockindex, buffer, buflen, nread); return t'1;
  refine seq_ex ge _ _ _ _ _ _ _
    (call_some ge _ _ (recvSpec c DB n p gv) _t'1 _ _ emptyEnv _ (H c DB n p gv) _ X.recv.b
      X.recv.fd (fun v => ∃ r, v = .Vint r)
      (fun v h => ∃ g, (v = .Vint Integers.Int.zero → g ≠ Integers.Int64.zero)
        ∧ H c DB n p (.Vlong g) h)
      (X.sRecv n p gv) X.recv.fp X.recv.ty rfl
      (fun le m _ => eval_callee_global rfl X.recv.sym rfl)
      (fun le m hT => .cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vptr c.dataB c.dataO) (hT.get (by temps_get))) rfl
        (.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ c.sockV (hT.get (by temps_get))) (X.sockCast m)
        (.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vptr c.bb Integers.Ptrofs.zero) (hT.get (by temps_get))) rfl
        (.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ v900 (hT.get (by temps_get))) rfl
        (.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vptr c.bg Integers.Ptrofs.zero) (hT.get (by temps_get))) rfl
          .nil)))))
      (fun h hH => ⟨rfl, hH⟩)
      (fun v h hs => by
        obtain ⟨r, g, rfl, hrg, hH⟩ := hs
        exact ⟨⟨r, rfl⟩, g, fun h0 => hrg (by injection h0), hH⟩))
    (fun v => triple_pure ge _ _ _ _ _ _ (fun hv => ?_))
  obtain ⟨r, rfl⟩ := hv
  exact triple_return_local ge _ _ _ _ _ _ (.Vint r) (.Vint r)
    (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _)))
    (fun _ => rfl)
    (fun hp ⟨g, hrg, hH⟩ => ⟨r, g, rfl, fun h0 => hrg (by rw [h0]), hH⟩)

/-! ## 関数全体 -/

/-- 引数（局所変数を確保したあとの一時変数）。 -/
abbrev lP (c : Ctx) : List (Ident × Val) :=
  [(_data, .Vptr c.dataB c.dataO), (_sockindex, c.sockV), (_pp, .Vptr c.ppB c.ppO),
   (_code, .Vptr c.codeB c.codeO), (_size, .Vptr c.sizeB c.sizeO)]

set_option maxHeartbeats 4000000 in
/-- **Case 1 の P1（C）**: 修正後の `Curl_pp_readresp` の本体は、受信バッファがどんな長さでも、
    呼ばれる側の関数が仕様の範囲でどう振る舞っても、return に達する。 -/
theorem readresp_returns (X : Ext c DB ge) (n : Nat) (p gv : Val) :
    Triple ge (FunctionEntry2 ge) f_Curl_pp_readresp
      (LocalSt (envE c.bg c.bb) (lP c) (H c DB n p gv)) f_Curl_pp_readresp.fn_body
      (RetOK Sep.Assn.no Sep.Assn.no Sep.Assn.no) := by
  -- conn = data->conn;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ _ _ _ _conn _ c.connV (fun le m hp hT hH hag => ?_)) ?_
  · have h := eval_field (e := envE c.bg c.bb) (p := _data) (b := c.dataB) (o := c.dataO)
      (ty := tptr (Ty.Tstruct _connectdata noattr))
      (hT.get (by temps_get))
      (by rw [X.cenv]; exact co_easy) (by rw [X.cenv]; exact off_conn) rfl
      (fixed_load (k := 3) (hk := by simp [cells]) rfl X.pmR hH hag)
    rwa [loadResult_ptr X.connPtr] at h
  -- result = CURLE_OK; maxloops = 10; *code = 0; *size = 0;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ _ _ _ _result _ (.Vint (Integers.Int.repr 0))
      (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ _ _ _ _maxloops _ (.Vint (Integers.Int.repr 10))
      (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (assign_cell ge _ _ c DB n p gv _ _ 1 (by simp [cells]) .Mint32 c.pm c.codeB c.codeO AnyV rfl
      _ _ X.pmW rfl
      (fun le m hT => EvalLvalue.Ederef _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))
      (fun le m hp hT _ _ => ⟨_, _, EvalExpr.Econst_int _ _, rfl, trivial⟩)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (assign_cell ge _ _ c DB n p gv _ _ 2 (by simp [cells]) .Mint64 c.pm c.sizeB c.sizeO AnyV rfl
      _ _ X.pmW rfl
      (fun le m hT => EvalLvalue.Ederef _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))
      (fun le m hp hT _ _ => ⟨_, _, EvalExpr.Econst_int _ _, rfl, trivial⟩)) ?_
  -- do { ... } while(gotbytes == sizeof(buffer));
  have hsub0 : ∀ q ∈ lI c (Integers.Int.repr ((10 : Nat) : _root_.Int)) (Integers.Int.repr 0),
      q ∈ setLocal (setLocal (setLocal (lP c) _conn c.connV) _result (.Vint (Integers.Int.repr 0)))
        _maxloops (.Vint (Integers.Int.repr 10)) := by
    intro q hq
    simp only [lI, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> temps_get
  refine Sep.triple_seq ge _ _ _ (OPost c DB) _ _ _ ?_ ?_
  · refine Sep.triple_pre ge _ _ (P := I1 c DB 10)
      (fun _ _ _ h => ⟨by decide, n, p, gv, _, lst_weaken hsub0 h⟩) ?_
    exact outer_loop X (pread_ok X) _ _ 10
  refine triple_exists ge _ _ _ _ _ (fun n1 => triple_exists ge _ _ _ _ _ (fun p1 =>
    triple_exists ge _ _ _ _ _ (fun gv1 => triple_exists ge _ _ _ _ _ (fun r =>
      triple_exists ge _ _ _ _ _ (fun mx => ?_)))))
  -- pp->pending_resp = FALSE;
  refine triple_seq_fwd ge _ _ _ (LocalSt (envE c.bg c.bb) (lI c mx r) (H c DB n1 p1 gv1)) _ _ _
    (Case2C.triple_assign_bitfield ge _ _ _ _ _ _ c.pm c.ppB
      (Integers.Ptrofs.add c.ppO (Integers.Ptrofs.repr 48)) 0 X.pmW X.pmR rfl (by decide)
      (by decide) (fun e le hp m hP hag => ?_)) ?_
  · obtain ⟨he, hT, hH⟩ := hP
    obtain ⟨v, h1, h2, hd, rfl, ⟨cv, rfl⟩, hm, hR⟩ :=
      cell_split (k := 9) (hk := by simp [cells]) rfl hH
    exact ⟨cv, Integers.Int.repr 0, h1, h2, hd, rfl, hm,
      EvalLvalue.Efield_struct _ _ _ _ _ _ _ _ _ _ (eval_deref_temp (hT.get (by temps_get))) rfl
        (by rw [X.cenv]; exact co_pp) (by rw [X.cenv]; exact off_pending),
      ⟨_, EvalExpr.Econst_int _ _, rfl⟩,
      fun h1' hm' hd' => ⟨he, hT, cell_join (k := 9) (hk := by simp [cells]) rfl hd' ⟨_, rfl⟩ hm' hR⟩⟩
  -- return result;
  exact ret_val ge _ X.cenv c X.bgbb DB n1 p1 gv1 _ _ (.Vint r) _ _ _
    (fun _ _ hT => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (fun _ => rfl)

end Case1C

#print axioms Case1C.readresp_returns
#print axioms Case1C.pread_ok
#print axioms Case1C.outer_loop
#print axioms Case1C.inner_loop
