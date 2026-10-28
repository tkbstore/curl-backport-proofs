/-
Case 1: 修正後の `Curl_pp_readresp` の外側のループと、関数全体が止まること（P1）。

```c
do {
  gotbytes = 0;
  if(pp->nfinal) { ...; curlx_dyn_tail(&pp->recvbuf, full - pp->nfinal); pp->nfinal = 0; }
  if(!pp->overflow) { if(!maxloops--) return CURLE_OK; ... 読む ... }   /* Case1Ovf */
  while(...) { ... 1行ずつ取り出す ... }                              /* Case1Inner */
} while(gotbytes == sizeof(buffer));
pp->pending_resp = FALSE;
return result;
```

減少量は `maxloops`（10 から始まる）。ループが続くのは `gotbytes == sizeof(buffer)` のときだけで、
そのときは必ずソケットから読んでおり、`maxloops` が1つ減っている（`J1`）。
-/
import Case1Ovf
open CC CC.Sep CC.HProp
open Case1_after
open Case5C (addr eval_field boolVal_ofBool_tint boolVal_ofBool_tbool)
open Case4C (IsPtr cast_ptr lv_field eval_deref_temp loadResult_ptr)

set_option maxRecDepth 20000

namespace Case1C

variable {ge : CGenv} {c : Ctx} {DB : Nat → Val → HProp}

/-- 外側のループの不変条件。`maxloops` が `N`。 -/
def I1 (c : Ctx) (DB : Nat → Val → HProp) (N : Nat) : Sep.Assn :=
  fun e le hp => N ≤ 10 ∧ ∃ n p gv r,
    LocalSt (envE c.bg c.bb) (lI c (Integers.Int.repr (N : _root_.Int)) r) (H c DB n p gv) e le hp

/-- 外側のループを抜けたあと。 -/
def OPost (c : Ctx) (DB : Nat → Val → HProp) : Sep.Assn :=
  fun e le hp => ∃ n p gv r mx,
    LocalSt (envE c.bg c.bb) (lI c mx r) (H c DB n p gv) e le hp

/-- `lI` を含む一時変数の並びと、そのときのメモリ。 -/
def St (c : Ctx) (DB : Nat → Val → HProp) (mx r : Integers.Int) (gv : Val) : Sep.Assn :=
  fun e le hp => ∃ n p l', (∀ q ∈ lI c mx r, q ∈ l')
    ∧ LocalSt (envE c.bg c.bb) l' (H c DB n p gv) e le hp

/-! ## `if(pp->nfinal) { ... }` -/

set_option maxHeartbeats 4000000 in
theorem nfin_ok (X : Ext c DB ge) (l : List (Ident × Val)) (mx r : Integers.Int) (n : Nat)
    (p gv : Val) (x : Integers.Int64)
    (hsub : ∀ q ∈ lI c mx r, q ∈ l) (h27 : (_t'27, Val.Vlong x) ∈ l) :
    Triple ge (FunctionEntry2 ge) f_Curl_pp_readresp
      (LocalSt (envE c.bg c.bb) l (H c DB n p gv)) nfinIf (.only (St c DB mx r gv)) := by
  have hpp : (_pp, Val.Vptr c.ppB c.ppO) ∈ l := hsub _ (by simp)
  cases hx : Integers.Int64.eq x Integers.Int64.zero with
  | true =>
    refine triple_if_local ge _ _ _ _ _ _ false _ _ _
      (fun le m _ hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get h27),
        by show Cop.boolVal (.Vlong x) tulong m = _; rw [boolVal_long, hx]; rfl⟩) ?_
    exact Sep.triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x)
      (fun _ _ _ h => ⟨n, p, l, hsub, h⟩)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
  | false =>
  refine triple_if_local ge _ _ _ _ _ _ true _ _ _
    (fun le m _ hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get h27),
      by show Cop.boolVal (.Vlong x) tulong m = _; rw [boolVal_long, hx]; rfl⟩) ?_
  -- full = curlx_dyn_len(&pp->recvbuf);
  refine Sep.triple_seq ge _ _ _
    (LocalSt (envE c.bg c.bb)
      (setLocal (setLocal l _t'1 (.Vlong (Integers.Int64.repr n))) _full
        (.Vlong (Integers.Int64.repr n))) (H c DB n p gv)) _ _ _ ?_ ?_
  · refine triple_weaken_only ge _ _ ?_
    refine call_some_then (lenSpec c DB n p gv) _t'1 _ _ _ l _ [rbV c] X.len.b X.len.fd
      (fun v => v = .Vlong (Integers.Int64.repr n)) (fun _ => H c DB n p gv) _ _
      (X.sLen n p gv) X.len.fp X.len.ty rfl (fun le m _ => ev_callee X.len rfl)
      (fun le m hT => args_rb X (hT.get hpp)) (fun h hH => ⟨rfl, hH⟩) (fun v h hs => hs)
      (fun v hv => ?_)
    subst hv
    exact triple_set_local_fwd ge _ _ _ _ _ _full _ _
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _)))
  -- t'28 = pp->nfinal; curlx_dyn_tail(&pp->recvbuf, full - t'28); pp->nfinal = 0;
  refine Sep.triple_seq ge _ _ _
    (fun e le hp => ∃ a p', LocalSt (envE c.bg c.bb)
      (setLocal (setLocal (setLocal l _t'1 (.Vlong (Integers.Int64.repr n))) _full
        (.Vlong (Integers.Int64.repr n))) _t'28 (.Vlong a))
      (H c DB (tailLen n (Integers.Int64.sub (Integers.Int64.repr n) a)) p' gv) e le hp)
    _ _ _ ?_ ?_
  · refine triple_weaken_only ge _ _ ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (set_any _ _ _ _t'28 _ IsLong (fun le m hp hT hH hag =>
        ev_ppfield X (k := 7) (hk := by simp [cells]) rfl off_nfinal (hT.get (by tget hpp)) hH hag))
      ?_
    refine triple_exists ge _ _ _ _ _ (fun v => triple_pure ge _ _ _ _ _ _ (fun hv => ?_))
    obtain ⟨a, rfl⟩ := hv
    refine Sep.triple_conseq ge _ _
      (call_none ge _ _ (tailSpec c DB n p gv (Integers.Int64.sub (Integers.Int64.repr n) a)) _ _ _
        _ _ [rbV c, .Vlong (Integers.Int64.sub (Integers.Int64.repr n) a)] X.tail.b X.tail.fd
        (fun _ => True)
        (fun _ h => ∃ p', H c DB (tailLen n (Integers.Int64.sub (Integers.Int64.repr n) a)) p' gv h)
        (X.sTail n p gv _) X.tail.fp X.tail.ty rfl (fun le m _ => ev_callee X.tail rfl)
        (fun le m hT => .cons _ _ _ _ _ _ _ (ev_rb X (hT.get (by tget hpp))) rfl
          (.cons _ _ _ _ _ _ _
            (EvalExpr.Ebinop _ _ _ _ _ _ _
              (EvalExpr.Etempvar _ _ (.Vlong (Integers.Int64.repr n)) (hT.get (by temps_get)))
              (EvalExpr.Etempvar _ _ (.Vlong a) (hT.get (mem_setLocal_head _ _ _))) rfl)
            rfl .nil))
        (fun h hH => ⟨rfl, hH⟩) (fun v h hs => ⟨trivial, hs.2⟩))
      (fun _ _ _ x => x)
      (fun _ _ _ h => by
        obtain ⟨_, _, he, hT, p', hH⟩ := h
        exact ⟨a, p', he, hT, hH⟩)
      (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
  refine triple_exists ge _ _ _ _ _ (fun a => triple_exists ge _ _ _ _ _ (fun p' => ?_))
  exact Sep.triple_conseq ge _ _
    (assign_cell ge _ _ c DB _ p' gv _ _ 7 (by simp [cells]) .Mint64 c.pm c.ppB
      (Integers.Ptrofs.add c.ppO (Integers.Ptrofs.repr 32)) IsLong rfl _ _ X.pmW rfl
      (fun le m hT => lv_pp X off_nfinal (hT.get (by tget hpp)))
      (fun le m hp hT _ _ => ⟨_, _, EvalExpr.Econst_int _ _, rfl, ⟨_, rfl⟩⟩))
    (fun _ _ _ x => x)
    (fun _ _ _ h => ⟨_, p', _,
      sub_setLocal (sub_setLocal (sub_setLocal hsub (by lI_ne)) (by lI_ne)) (by lI_ne), h⟩)
    (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)

/-! ## 外側のループの本体と条件 -/

/-- 外側のループ全体の出口（ループの外に出たら `OPost`、関数から戻るのは何でもよい）。 -/
abbrev RL (c : Ctx) (DB : Nat → Val → HProp) (B C : Sep.Assn) : Sep.ExitConds :=
  RetOK (OPost c DB) B C

set_option maxHeartbeats 4000000 in
theorem outer_body (X : Ext c DB ge)
    (hPr : ∀ n p gv vs, SatisfiesAt ge (FunctionEntry2 ge) X.pread.fd (recvSpec c DB n p gv) vs)
    (B C : Sep.Assn) (N : Nat) :
    Triple ge (FunctionEntry2 ge) f_Curl_pp_readresp (I1 c DB N) outerBody
      { normal := J1 c DB N, brk := (RL c DB B C).normal, cont := J1 c DB N,
        ret := (RL c DB B C).ret, goto := (RL c DB B C).goto } := by
  refine triple_pure ge _ _ _ _ _ _ (fun hN => ?_)
  refine triple_exists ge _ _ _ _ _ (fun n => triple_exists ge _ _ _ _ _ (fun p =>
    triple_exists ge _ _ _ _ _ (fun gv => triple_exists ge _ _ _ _ _ (fun r => ?_))))
  have hpp : (_pp, Val.Vptr c.ppB c.ppO) ∈ lI c (Integers.Int.repr (N : _root_.Int)) r := by simp
  -- gotbytes = 0;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (assign_got ge _ _ c DB n p gv _ _ (envE_got c.bg c.bb) _ vzero
      (fun le m _ => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)) ?_
  -- t'27 = pp->nfinal; if(t'27) { ... }
  refine Sep.triple_seq ge _ _ _ (St c DB (Integers.Int.repr (N : _root_.Int)) r vzero) _ _ _ ?_ ?_
  · refine triple_weaken_only ge _ _ ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (set_any _ _ _ _t'27 _ IsLong (fun le m hp hT hH hag =>
        ev_ppfield X (k := 7) (hk := by simp [cells]) rfl off_nfinal (hT.get hpp) hH hag)) ?_
    refine triple_exists ge _ _ _ _ _ (fun v => triple_pure ge _ _ _ _ _ _ (fun hv => ?_))
    obtain ⟨x, rfl⟩ := hv
    exact nfin_ok X _ _ r n p vzero x (sub_setLocal (fun _ x => x) (by lI_ne))
      (mem_setLocal_head _ _ _)
  refine triple_exists ge _ _ _ _ _ (fun n1 => triple_exists ge _ _ _ _ _ (fun p1 =>
    triple_exists ge _ _ _ _ _ (fun l1 => triple_pure ge _ _ _ _ _ _ (fun hsub1 => ?_))))
  -- t'19 = pp->overflow; if(!t'19) { ... }
  refine Sep.triple_seq ge _ _ _ (J1 c DB N) _ _ _ ?_ ?_
  · refine triple_seq_fwd ge _ _ _ _ _ _ _
      (set_any _ _ _ _t'19 _ IsLong (fun le m hp hT hH hag =>
        ev_ppfield X (k := 6) (hk := by simp [cells]) rfl off_overflow (hT.get (hsub1 _ hpp)) hH hag))
      ?_
    refine triple_exists ge _ _ _ _ _ (fun v => triple_pure ge _ _ _ _ _ _ (fun hv => ?_))
    obtain ⟨x, rfl⟩ := hv
    exact ovf_ok X hPr _ N hN r n1 p1 x _ _ (sub_setLocal hsub1 (by lI_ne)) (mem_setLocal_head _ _ _)
  -- 内側のループ
  refine triple_exists ge _ _ _ _ _ (fun n2 => triple_exists ge _ _ _ _ _ (fun p2 =>
    triple_exists ge _ _ _ _ _ (fun r2 => triple_exists ge _ _ _ _ _ (fun mx =>
      triple_exists ge _ _ _ _ _ (fun g => triple_pure ge _ _ _ _ _ _ (fun hcond => ?_))))))
  refine Sep.triple_pre ge _ _ (P := I2 c DB mx (.Vlong g) n2)
    (fun _ _ _ h => ⟨p2, r2, h⟩) ?_
  refine Sep.triple_conseq ge _ _ (inner_loop X mx (.Vlong g) (OPost c DB) (J1 c DB N) n2)
    (fun _ _ _ x => x) ?_ (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
  intro e le hp ⟨n3, p3, r3, gv3, hor, h⟩
  rcases hor with rfl | rfl
  · exact ⟨n3, p3, r3, mx, g, hcond, h⟩
  · exact ⟨n3, p3, r3, mx, Integers.Int64.repr 0,
      fun h0 => absurd h0 (by rw [zero_ne_900]; decide), h⟩

theorem outer_cond (X : Ext c DB ge) (B C : Sep.Assn) (N : Nat) :
    Triple ge (FunctionEntry2 ge) f_Curl_pp_readresp (J1 c DB N) outerCond
      { normal := fun e le hp => ∃ N', N' < N ∧ I1 c DB N' e le hp,
        brk := (RL c DB B C).normal, cont := Sep.Assn.no,
        ret := (RL c DB B C).ret, goto := (RL c DB B C).goto } := by
  refine triple_exists ge _ _ _ _ _ (fun n => triple_exists ge _ _ _ _ _ (fun p =>
    triple_exists ge _ _ _ _ _ (fun r => triple_exists ge _ _ _ _ _ (fun mx =>
      triple_exists ge _ _ _ _ _ (fun g => triple_pure ge _ _ _ _ _ _ (fun hcond => ?_))))))
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ _ _ _ _t'16 _ (.Vlong g)
      (fun le m hp hT hH hag => ev_got hH hag)) ?_
  cases h9 : Integers.Int64.eq g c900 with
  | true =>
    refine triple_if_local ge _ _ _ _ _ _ true _ _ _
      (fun le m _ hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _))) (ev_size X) (eq900 _ _ _),
        by rw [h9]; exact boolVal_ofBool_tint true m⟩) ?_
    obtain ⟨N', hlt, hle, rfl⟩ := hcond h9
    exact Sep.triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x)
      (fun _ _ _ h => ⟨N', hlt, hle, n, p, _, r,
        lst_weaken (sub_setLocal (fun _ x => x) (by lI_ne)) h⟩)
      (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
  | false =>
    refine triple_if_local ge _ _ _ _ _ _ false _ _ _
      (fun le m _ hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _))) (ev_size X) (eq900 _ _ _),
        by rw [h9]; exact boolVal_ofBool_tint false m⟩) ?_
    exact Sep.triple_conseq ge _ _ (triple_break ge _ _ _) (fun _ _ _ x => x)
      (fun _ _ _ x => False.elim x)
      (fun _ _ _ h => ⟨n, p, _, r, mx, lst_weaken (sub_setLocal (fun _ x => x) (by lI_ne)) h⟩)
      (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)

/-- **外側のループは止まる**（`maxloops` が減少量）。 -/
theorem outer_loop (X : Ext c DB ge)
    (hPr : ∀ n p gv vs, SatisfiesAt ge (FunctionEntry2 ge) X.pread.fd (recvSpec c DB n p gv) vs)
    (B C : Sep.Assn) :
    ∀ N, Triple ge (FunctionEntry2 ge) f_Curl_pp_readresp (I1 c DB N)
      (.Sloop outerBody outerCond) (RL c DB B C) :=
  Sep.triple_loop ge _ _ (RL c DB B C) (I1 c DB) (J1 c DB) outerBody outerCond
    (outer_body X hPr B C) (outer_cond X B C)

end Case1C
