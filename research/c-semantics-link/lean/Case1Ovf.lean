/-
Case 1: 外側のループの本体のうち、ソケットから読む部分（`ovfIf`）。

```c
if(!pp->overflow) {
  if(!maxloops--)          /* 修正で入った上限 */
    return CURLE_OK;
  result = pingpong_read(data, sockindex, buffer, sizeof(buffer), &gotbytes);
  if(result == CURLE_AGAIN) return CURLE_OK;
  if(result) return result;
  if(!gotbytes) { failf(...); return CURLE_RECV_ERROR; }   /* 前提で除いた経路（Case1Spec） */
  result = curlx_dyn_addn(&pp->recvbuf, buffer, gotbytes);
  if(result) return result;
  data->req.headerbytecount += (unsigned int)gotbytes;
  pp->nread_resp += gotbytes;
}
```

読んだときは `maxloops` が1つ減る。読まないときは `gotbytes` が 0 のまま残る。
外側のループが続くのは `gotbytes == sizeof(buffer)` のときだけなので、どちらでも減少量が保てる。
-/
import Case1Inner
open CC CC.Sep CC.HProp
open Case1_after
open Case5C (addr eval_field boolVal_ofBool_tint boolVal_ofBool_tbool)
open Case4C (IsPtr cast_ptr lv_field eval_deref_temp)

set_option maxRecDepth 20000

namespace Case1C

variable {ge : CGenv} {c : Ctx} {DB : Nat → Val → HProp}

/-- 一時変数の並びから取り出す。`h` は抽象した並びに入っていることの証拠。 -/
macro "tget " h:term : tactic =>
  `(tactic| repeat (first
      | exact $h
      | exact CC.Sep.mem_setLocal_head _ _ _
      | refine CC.Sep.mem_setLocal_of_mem' ?_ (by decide)))

/-- `sizeof(buffer)` を 64 ビットの整数にしたもの。 -/
def c900 : Integers.Int64 := Integers.Ptrofs.to_int64 (Integers.Ptrofs.repr 900)

/-- 外側のループの本体のあと（`while` の条件を見る前）。
    `gotbytes == sizeof(buffer)` なら、`maxloops` は `N` より小さい `N'` になっている。 -/
def J1 (c : Ctx) (DB : Nat → Val → HProp) (N : Nat) : Sep.Assn :=
  fun e le hp => ∃ n p r mx g,
    (Integers.Int64.eq g c900 = true →
      ∃ N' : Nat, N' < N ∧ N' ≤ 10 ∧ mx = Integers.Int.repr (N' : _root_.Int))
    ∧ LocalSt (envE c.bg c.bb) (lI c mx r) (H c DB n p (.Vlong g)) e le hp

/-- 読んだあと。`gotbytes` は 0 でない。 -/
def RdPost (c : Ctx) (DB : Nat → Val → HProp) (mx : Integers.Int) : Sep.Assn :=
  fun e le hp => ∃ n p r g, g ≠ Integers.Int64.zero
    ∧ LocalSt (envE c.bg c.bb) (lI c mx r) (H c DB n p (.Vlong g)) e le hp

/-! ## 式の値 -/

theorem ev_got {le : TempEnv} {m : Mem} {hp : Heap} {n : Nat} {p : Val} {g : Integers.Int64}
    (hH : H c DB n p (.Vlong g) hp) (hag : Heap.Agrees hp m) :
    EvalExpr ge (envE c.bg c.bb) le m (.Evar _gotbytes tulong) (.Vlong g) :=
  EvalExpr.Elvalue _ _ _ _ _ (EvalLvalue.Evar_local _ _ _ (envE_got c.bg c.bb))
    (DerefLoc.value .Mint64 _ rfl (by
      show Mem.load .Mint64 m c.bg (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) = _
      rw [ptrofs_unsigned_zero]
      exact got_load hH hag))

theorem ev_buf {le : TempEnv} {m : Mem} :
    EvalExpr ge (envE c.bg c.bb) le m (.Evar _buffer (tarray tschar 900))
      (.Vptr c.bb Integers.Ptrofs.zero) :=
  EvalExpr.Elvalue _ _ _ _ _ (EvalLvalue.Evar_local _ _ _ (envE_buf c.bg c.bb))
    (DerefLoc.reference rfl)

theorem ev_gaddr {le : TempEnv} {m : Mem} :
    EvalExpr ge (envE c.bg c.bb) le m (.Eaddrof (.Evar _gotbytes tulong) (tptr tulong))
      (.Vptr c.bg Integers.Ptrofs.zero) :=
  EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _ (envE_got c.bg c.bb))

theorem ev_size (X : Ext c DB ge) {le : TempEnv} {m : Mem} :
    EvalExpr ge (envE c.bg c.bb) le m (.Esizeof (tarray tschar 900) tulong) v900 := by
  have h := EvalExpr.Esizeof (ge := ge) (e := envE c.bg c.bb) (le := le) (m := m)
    (tarray tschar 900) tulong
  rw [X.cenv, sizeof_buffer] at h
  exact h

theorem eq81 (ce : CompositeEnv) (m : Mem) (r : Integers.Int) :
    Cop.semBinaryOperation ce .Oeq (.Vint r) tint (.Vint (Integers.Int.repr 81)) tint m
      = some (Val.ofBool (Integers.Int.eq r (Integers.Int.repr 81))) := rfl

theorem eq900 (ce : CompositeEnv) (m : Mem) (g : Integers.Int64) :
    Cop.semBinaryOperation ce .Oeq (.Vlong g) tulong v900 tulong m
      = some (Val.ofBool (Integers.Int64.eq g c900)) := rfl

theorem notbool_long (x : Integers.Int64) (m : Mem) :
    Cop.semUnaryOperation .Onotbool (.Vlong x) tulong m
      = some (Val.ofBool (!(!Integers.Int64.eq x Integers.Int64.zero))) := rfl

theorem notbool_int (x : Integers.Int) (m : Mem) :
    Cop.semUnaryOperation .Onotbool (.Vint x) tint m
      = some (Val.ofBool (!(!Integers.Int.eq x Integers.Int.zero))) := rfl

theorem boolVal_long (x : Integers.Int64) (m : Mem) :
    Cop.boolVal (.Vlong x) tulong m = some (!Integers.Int64.eq x Integers.Int64.zero) := rfl

theorem boolVal_int (r : Integers.Int) (m : Mem) :
    Cop.boolVal (.Vint r) tint m = some (!Integers.Int.eq r Integers.Int.zero) := rfl

theorem int_eq_zero {r : Integers.Int} (h : Integers.Int.eq r Integers.Int.zero = true) :
    r = Integers.Int.zero := by
  unfold Integers.Int.eq Integers.MI.eq at h
  exact beq_iff_eq.mp h

theorem long_eq_false {g : Integers.Int64} (h : g ≠ Integers.Int64.zero) :
    Integers.Int64.eq g Integers.Int64.zero = false := by
  cases hb : Integers.Int64.eq g Integers.Int64.zero with
  | false => rfl
  | true =>
    unfold Integers.Int64.eq Integers.MI.eq at hb
    exact absurd (beq_iff_eq.mp hb) h

theorem zero_ne_900 : Integers.Int64.eq (Integers.Int64.repr 0) c900 = false := by decide

/-- `maxloops` の値（0 から 10 まで）。 -/
theorem ml_zero : Integers.Int.eq (Integers.Int.repr ((0 : Nat) : _root_.Int)) Integers.Int.zero = true := by
  decide

theorem ml_pos (N : Nat) (h1 : 1 ≤ N) (h : N ≤ 10) :
    Integers.Int.eq (Integers.Int.repr (N : _root_.Int)) Integers.Int.zero = false
    ∧ Integers.Int.sub (Integers.Int.repr (N : _root_.Int)) (Integers.Int.repr 1)
        = Integers.Int.repr ((N - 1 : Nat) : _root_.Int) := by
  have : N = 1 ∨ N = 2 ∨ N = 3 ∨ N = 4 ∨ N = 5 ∨ N = 6 ∨ N = 7 ∨ N = 8 ∨ N = 9 ∨ N = 10 := by
    omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-! ## 一時変数 -/

theorem lst_ex_pure {α : Sort u} {E : Env} {l : List (Ident × Val)} {φ : α → Prop}
    {Q : α → HProp} {e : Env} {le : TempEnv} {hp : Heap}
    (h : LocalSt E l (fun h => ∃ a, φ a ∧ Q a h) e le hp) :
    ∃ a, φ a ∧ LocalSt E l (Q a) e le hp := by
  obtain ⟨he, hT, a, hφ, hQ⟩ := h
  exact ⟨a, hφ, he, hT, hQ⟩

theorem lst_ex2 {α β : Sort u} {E : Env} {l : List (Ident × Val)} {Q : α → β → HProp}
    {e : Env} {le : TempEnv} {hp : Heap}
    (h : LocalSt E l (fun h => ∃ a b, Q a b h) e le hp) :
    ∃ a b, LocalSt E l (Q a b) e le hp := by
  obtain ⟨he, hT, a, b, hQ⟩ := h
  exact ⟨a, b, he, hT, hQ⟩

/-- `maxloops` を書き換えたあとも、`lI` の他の一時変数は残る。 -/
theorem lI_set_ml {l : List (Ident × Val)} {mx mx1 r : Integers.Int}
    (hsub : ∀ q ∈ lI c mx r, q ∈ l) : ∀ q ∈ lI c mx1 r, q ∈ setLocal l _maxloops (.Vint mx1) := by
  intro q hq
  simp only [lI, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_setLocal_of_mem' (hsub _ (by simp)) (by decide)
  · exact mem_setLocal_of_mem' (hsub _ (by simp)) (by decide)
  · exact mem_setLocal_of_mem' (hsub _ (by simp)) (by decide)
  · exact mem_setLocal_of_mem' (hsub _ (by simp)) (by decide)
  · exact mem_setLocal_of_mem' (hsub _ (by simp)) (by decide)
  · exact mem_setLocal_of_mem' (hsub _ (by simp)) (by decide)
  · exact mem_setLocal_head _ _ _
  · exact mem_setLocal_of_mem' (hsub _ (by simp)) (by decide)

/-! ## `data->req.headerbytecount` -/

theorem ev_req (X : Ext c DB ge) {le : TempEnv} {m : Mem}
    (hdata : le.get _data = some (.Vptr c.dataB c.dataO)) :
    EvalExpr ge (envE c.bg c.bb) le m
      (.Efield (.Ederef (.Etempvar _data tyEasy) (.Tstruct _Curl_easy noattr)) _req
        (.Tstruct _SingleRequest noattr))
      (.Vptr c.dataB (Integers.Ptrofs.add c.dataO (Integers.Ptrofs.repr 8))) :=
  EvalExpr.Elvalue _ _ _ _ _
    (lv_field (eval_deref_temp hdata) rfl (by rw [X.cenv]; exact co_easy)
      (by rw [X.cenv]; exact off_req))
    (DerefLoc.copy rfl)

theorem lv_hbc (X : Ext c DB ge) {le : TempEnv} {m : Mem}
    (hdata : le.get _data = some (.Vptr c.dataB c.dataO)) :
    EvalLvalue ge (envE c.bg c.bb) le m
      (.Efield (.Efield (.Ederef (.Etempvar _data tyEasy) (.Tstruct _Curl_easy noattr)) _req
        (.Tstruct _SingleRequest noattr)) _headerbytecount tuint) c.dataB
      (Integers.Ptrofs.add (Integers.Ptrofs.add c.dataO (Integers.Ptrofs.repr 8))
        (Integers.Ptrofs.repr 0)) .Full :=
  lv_field (ev_req X hdata) rfl (by rw [X.cenv]; exact co_req) (by rw [X.cenv]; exact off_hbc)

theorem hbc_ok (X : Ext c DB ge) (l : List (Ident × Val)) (n : Nat) (p : Val) (g : Integers.Int64)
    (hdata : (_data, Val.Vptr c.dataB c.dataO) ∈ l) :
    Triple ge (FunctionEntry2 ge) f_Curl_pp_readresp
      (LocalSt (envE c.bg c.bb) l (H c DB n p (.Vlong g))) hbcUpd
      (.only (fun e le hp => ∃ v22, LocalSt (envE c.bg c.bb)
        (setLocal (setLocal l _t'22 v22) _t'23 (.Vlong g)) (H c DB n p (.Vlong g)) e le hp)) := by
  refine Sep.triple_seq ge _ _ _
    (fun e le hp => ∃ v, IsInt v ∧ LocalSt (envE c.bg c.bb) (setLocal l _t'22 v)
      (H c DB n p (.Vlong g)) e le hp) _ _ _ ?_ ?_
  · refine triple_weaken_only ge _ _
      (set_any _ _ _ _t'22 _ IsInt (fun le m hp hT hH hag => ?_))
    obtain ⟨v, hv, hload⟩ := cell_load (k := 4) (hk := by simp [cells]) rfl X.pmR hH hag
    obtain ⟨x, rfl⟩ := hv
    exact ⟨_, ⟨x, rfl⟩, EvalExpr.Elvalue _ _ _ _ _ (lv_hbc X (hT.get hdata))
      (DerefLoc.value .Mint32 _ rfl hload)⟩
  refine triple_exists ge _ _ _ _ _ (fun v => triple_pure ge _ _ _ _ _ _ (fun hv => ?_))
  obtain ⟨a, rfl⟩ := hv
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ _ _ _ _t'23 _ (.Vlong g)
      (fun le m hp hT hH hag => ev_got hH hag)) ?_
  exact Sep.triple_conseq ge _ _
    (assign_cell ge _ _ c DB n p (.Vlong g) _ _ 4 (by simp [cells]) .Mint32 c.pm c.dataB
      (Integers.Ptrofs.add (Integers.Ptrofs.add c.dataO (Integers.Ptrofs.repr 8))
        (Integers.Ptrofs.repr 0)) IsInt rfl _ _ X.pmW rfl
      (fun le m hT => lv_hbc X (hT.get (by tget hdata)))
      (fun le m hp hT _ _ => ⟨_, _, EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ (.Vint a) (hT.get (by tget hdata)))
        (EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ (.Vlong g) (hT.get (mem_setLocal_head _ _ _)))
          rfl) rfl, rfl, ⟨_, rfl⟩⟩))
    (fun _ _ _ x => x) (fun _ _ _ h => ⟨_, h⟩)
    (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)

/-! ## `pp->nread_resp += gotbytes;` -/

theorem nr_ok (X : Ext c DB ge) (l : List (Ident × Val)) (n : Nat) (p : Val) (g : Integers.Int64)
    (hpp : (_pp, Val.Vptr c.ppB c.ppO) ∈ l) :
    Triple ge (FunctionEntry2 ge) f_Curl_pp_readresp
      (LocalSt (envE c.bg c.bb) l (H c DB n p (.Vlong g))) nrUpd
      (.only (fun e le hp => ∃ v20, LocalSt (envE c.bg c.bb)
        (setLocal (setLocal l _t'20 v20) _t'21 (.Vlong g)) (H c DB n p (.Vlong g)) e le hp)) := by
  refine Sep.triple_seq ge _ _ _
    (fun e le hp => ∃ v, IsLong v ∧ LocalSt (envE c.bg c.bb) (setLocal l _t'20 v)
      (H c DB n p (.Vlong g)) e le hp) _ _ _ ?_ ?_
  · exact triple_weaken_only ge _ _
      (set_any _ _ _ _t'20 _ IsLong (fun le m hp hT hH hag =>
        ev_ppfield X (k := 5) (hk := by simp [cells]) rfl off_nread (hT.get hpp) hH hag))
  refine triple_exists ge _ _ _ _ _ (fun v => triple_pure ge _ _ _ _ _ _ (fun hv => ?_))
  obtain ⟨a, rfl⟩ := hv
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ _ _ _ _t'21 _ (.Vlong g)
      (fun le m hp hT hH hag => ev_got hH hag)) ?_
  exact Sep.triple_conseq ge _ _
    (assign_cell ge _ _ c DB n p (.Vlong g) _ _ 5 (by simp [cells]) .Mint64 c.pm c.ppB
      (Integers.Ptrofs.add c.ppO (Integers.Ptrofs.repr 0)) IsLong rfl _ _ X.pmW rfl
      (fun le m hT => lv_pp X off_nread (hT.get (by tget hpp)))
      (fun le m hp hT _ _ => ⟨_, _, EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ (.Vlong a) (hT.get (by tget hpp)))
        (EvalExpr.Etempvar _ _ (.Vlong g) (hT.get (mem_setLocal_head _ _ _))) rfl, rfl,
        ⟨_, rfl⟩⟩))
    (fun _ _ _ x => x) (fun _ _ _ h => ⟨_, h⟩)
    (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)

/-! ## 読む部分（`readStmt`） -/

/-- `if(result) return result;`（`result` は `r`）。0 のときは事実 `r = 0` を残して抜ける。 -/
theorem ret_if_nz (X : Ext c DB ge) (l : List (Ident × Val)) (n : Nat) (p gv : Val)
    (r : Integers.Int) (Q B C : Sep.Assn) (hr : (_result, Val.Vint r) ∈ l)
    (hQ : ∀ e le hp, r = Integers.Int.zero →
      LocalSt (envE c.bg c.bb) l (H c DB n p gv) e le hp → Q e le hp) :
    Triple ge (FunctionEntry2 ge) f_Curl_pp_readresp
      (LocalSt (envE c.bg c.bb) l (H c DB n p gv))
      (.Sifthenelse (.Etempvar _result tint) (.Sreturn (some (.Etempvar _result tint))) .Sskip)
      (RetOK Q B C) := by
  cases hz : Integers.Int.eq r Integers.Int.zero with
  | false =>
    refine triple_if_local ge _ _ _ _ _ _ true _ _ _
      (fun le m _ hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get hr),
        by show Cop.boolVal (.Vint r) tint m = _; rw [boolVal_int, hz]; rfl⟩) ?_
    exact ret_val ge _ X.cenv c X.bgbb DB n p gv _ _ (.Vint r) _ _ _
      (fun _ _ hT => EvalExpr.Etempvar _ _ _ (hT.get hr)) (fun _ => rfl)
  | true =>
    refine triple_if_local ge _ _ _ _ _ _ false _ _ _
      (fun le m _ hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get hr),
        by show Cop.boolVal (.Vint r) tint m = _; rw [boolVal_int, hz]; rfl⟩) ?_
    exact Sep.triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x)
      (fun e le hp h => hQ e le hp (int_eq_zero hz) h)
      (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)

set_option maxHeartbeats 4000000 in
theorem read_ok (X : Ext c DB ge)
    (hPr : ∀ n p gv vs, SatisfiesAt ge (FunctionEntry2 ge) X.pread.fd (recvSpec c DB n p gv) vs)
    (l : List (Ident × Val)) (mx r0 : Integers.Int) (n : Nat) (p gv : Val) (B C : Sep.Assn)
    (hsub : ∀ q ∈ lI c mx r0, q ∈ l) :
    Triple ge (FunctionEntry2 ge) f_Curl_pp_readresp
      (LocalSt (envE c.bg c.bb) l (H c DB n p gv)) readStmt (RetOK (RdPost c DB mx) B C) := by
  have hdata : (_data, Val.Vptr c.dataB c.dataO) ∈ l := hsub _ (by simp)
  have hsock : (_sockindex, c.sockV) ∈ l := hsub _ (by simp)
  have hpp : (_pp, Val.Vptr c.ppB c.ppO) ∈ l := hsub _ (by simp)
  -- t'3 = pingpong_read(data, sockindex, buffer, sizeof(buffer), &gotbytes); result = t'3;
  refine Sep.triple_seq ge _ _ _
    (fun e le hp => ∃ r g, (r = Integers.Int.zero → g ≠ Integers.Int64.zero) ∧
      LocalSt (envE c.bg c.bb) (setLocal (setLocal l _t'3 (.Vint r)) _result (.Vint r))
        (H c DB n p (.Vlong g)) e le hp) _ _ _ ?_ ?_
  · refine triple_weaken_only ge _ _ ?_
    refine call_some_then (recvSpec c DB n p gv) _t'3 _ _ _ l _
      [.Vptr c.dataB c.dataO, c.sockV, .Vptr c.bb Integers.Ptrofs.zero, v900,
       .Vptr c.bg Integers.Ptrofs.zero] X.pread.b X.pread.fd
      (fun v => ∃ r, v = .Vint r)
      (fun v h => ∃ g, (v = .Vint Integers.Int.zero → g ≠ Integers.Int64.zero)
        ∧ H c DB n p (.Vlong g) h) _ _
      (hPr n p gv) X.pread.fp X.pread.ty rfl (fun le m _ => ev_callee X.pread rfl)
      (fun le m hT => .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get hdata)) rfl
        (.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get hsock)) (X.sockCast m)
        (.cons _ _ _ _ _ _ _ ev_buf rfl
        (.cons _ _ _ _ _ _ _ (ev_size X) rfl
        (.cons _ _ _ _ _ _ _ ev_gaddr rfl .nil)))))
      (fun h hH => ⟨rfl, hH⟩)
      (fun v h hs => by
        obtain ⟨r, g, hv, hrg, hH⟩ := hs
        subst hv
        exact ⟨⟨r, rfl⟩, g, fun h0 => hrg (by injection h0), hH⟩)
      (fun v hv => ?_)
    obtain ⟨r, rfl⟩ := hv
    refine Sep.triple_pre ge _ _
      (P := fun e le hp => ∃ g, (Val.Vint r = .Vint Integers.Int.zero → g ≠ Integers.Int64.zero)
        ∧ LocalSt (envE c.bg c.bb) (setLocal l _t'3 (.Vint r)) (H c DB n p (.Vlong g)) e le hp)
      (fun _ _ _ h => lst_ex_pure h) ?_
    refine triple_exists ge _ _ _ _ _ (fun g => triple_pure ge _ _ _ _ _ _ (fun hrg => ?_))
    exact Sep.triple_conseq ge _ _
      (triple_set_local_fwd ge _ _ _ _ _ _result _ (.Vint r)
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _))))
      (fun _ _ _ x => x) (fun _ _ _ h => ⟨r, g, fun h0 => hrg (by rw [h0]), h⟩)
      (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
  refine triple_exists ge _ _ _ _ _ (fun r => triple_exists ge _ _ _ _ _ (fun g =>
    triple_pure ge _ _ _ _ _ _ (fun hrg => ?_)))
  have hsub1 : ∀ q ∈ lI c mx r, q ∈ setLocal (setLocal l _t'3 (.Vint r)) _result (.Vint r) :=
    lI_set_result (sub_setLocal hsub (by lI_ne))
  -- if(result == CURLE_AGAIN) return CURLE_OK;
  refine Sep.triple_seq ge _ _ _
    (LocalSt (envE c.bg c.bb) (setLocal (setLocal l _t'3 (.Vint r)) _result (.Vint r))
      (H c DB n p (.Vlong g))) _ _ _ ?_ ?_
  · cases hb : Integers.Int.eq r (Integers.Int.repr 81) with
    | true =>
      refine triple_if_local ge _ _ _ _ _ _ true _ _ _
        (fun le m _ hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _))) (EvalExpr.Econst_int _ _)
          (eq81 _ _ _), by rw [hb]; exact boolVal_ofBool_tint true m⟩) ?_
      exact ret_val ge _ X.cenv c X.bgbb DB n p _ _ _ (.Vint (Integers.Int.repr 0)) _ _ _
        (fun _ _ _ => EvalExpr.Econst_int _ _) (fun _ => rfl)
    | false =>
      refine triple_if_local ge _ _ _ _ _ _ false _ _ _
        (fun le m _ hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _))) (EvalExpr.Econst_int _ _)
          (eq81 _ _ _), by rw [hb]; exact boolVal_ofBool_tint false m⟩) ?_
      exact Sep.triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x)
        (fun _ _ _ x => x)
        (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
  -- if(result) return result;
  refine Sep.triple_seq ge _ _ _
    (fun e le hp => g ≠ Integers.Int64.zero ∧ LocalSt (envE c.bg c.bb)
      (setLocal (setLocal l _t'3 (.Vint r)) _result (.Vint r)) (H c DB n p (.Vlong g)) e le hp)
    _ _ _ ?_ ?_
  · exact ret_if_nz X _ n p _ r _ _ _ (mem_setLocal_head _ _ _)
      (fun _ _ _ hz h => ⟨hrg hz, h⟩)
  refine triple_pure ge _ _ _ _ _ _ (fun hg => ?_)
  -- if(!gotbytes) { ... }（gotbytes は 0 でないので通らない）
  refine Sep.triple_seq ge _ _ _
    (LocalSt (envE c.bg c.bb)
      (setLocal (setLocal (setLocal l _t'3 (.Vint r)) _result (.Vint r)) _t'25 (.Vlong g))
      (H c DB n p (.Vlong g))) _ _ _ ?_ ?_
  · refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ _ _ _ _t'25 _ (.Vlong g)
        (fun le m hp hT hH hag => ev_got hH hag)) ?_
    refine triple_if_local ge _ _ _ _ _ _ false _ _ _
      (fun le m _ hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
        (EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _))) (notbool_long _ _),
        by rw [long_eq_false hg]; exact boolVal_ofBool_tint false m⟩) ?_
    exact Sep.triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x)
      (fun _ _ _ x => x)
      (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
  -- t'24 = gotbytes; t'5 = curlx_dyn_addn(&pp->recvbuf, buffer, t'24); result = t'5;
  refine Sep.triple_seq ge _ _ _
    (fun e le hp => ∃ r5 n' p', LocalSt (envE c.bg c.bb)
      (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal l _t'3 (.Vint r)) _result
        (.Vint r)) _t'25 (.Vlong g)) _t'24 (.Vlong g)) _t'5 (.Vint r5)) _result (.Vint r5))
      (H c DB n' p' (.Vlong g)) e le hp) _ _ _ ?_ ?_
  · refine triple_weaken_only ge _ _ ?_
    refine Sep.triple_seq ge _ _ _
      (fun e le hp => ∃ r5 n' p', LocalSt (envE c.bg c.bb)
        (setLocal (setLocal (setLocal (setLocal (setLocal l _t'3 (.Vint r)) _result
          (.Vint r)) _t'25 (.Vlong g)) _t'24 (.Vlong g)) _t'5 (.Vint r5))
        (H c DB n' p' (.Vlong g)) e le hp) _ _ _ ?_ ?_
    · refine triple_weaken_only ge _ _ ?_
      refine triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ _ _ _ _t'24 _ (.Vlong g)
          (fun le m hp hT hH hag => ev_got hH hag)) ?_
      refine Sep.triple_conseq ge _ _
        (call_some ge _ _ (addnSpec c DB n p (.Vlong g)) _t'5 _ _ _ _ _
          [rbV c, .Vptr c.bb Integers.Ptrofs.zero, .Vlong g] X.addn.b X.addn.fd
          (fun v => ∃ r5, v = .Vint r5) (fun _ h => ∃ n' p', H c DB n' p' (.Vlong g) h)
          (X.sAddn n p _) X.addn.fp X.addn.ty rfl (fun le m _ => ev_callee X.addn rfl)
          (fun le m hT => .cons _ _ _ _ _ _ _ (ev_rb X (hT.get (by tget hpp))) rfl
            (.cons _ _ _ _ _ _ _ ev_buf rfl
            (.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _))) rfl
              .nil)))
          (fun h hH => ⟨rfl, hH⟩) (fun v h hs => hs))
        (fun _ _ _ x => x)
        (fun _ _ _ h => by
          obtain ⟨v, ⟨r5, rfl⟩, he, hT, n', p', hH⟩ := h
          exact ⟨r5, n', p', he, hT, hH⟩)
        (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
    · refine triple_exists ge _ _ _ _ _ (fun r5 => triple_exists ge _ _ _ _ _ (fun n' =>
        triple_exists ge _ _ _ _ _ (fun p' => ?_)))
      exact Sep.triple_conseq ge _ _
        (triple_set_local_fwd ge _ _ _ _ _ _result _ (.Vint r5)
          (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _))))
        (fun _ _ _ x => x) (fun _ _ _ h => ⟨r5, n', p', h⟩)
        (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
  refine triple_exists ge _ _ _ _ _ (fun r5 => triple_exists ge _ _ _ _ _ (fun n' =>
    triple_exists ge _ _ _ _ _ (fun p' => ?_)))
  have hsub3 : ∀ q ∈ lI c mx r5,
      q ∈ setLocal (setLocal (setLocal (setLocal (setLocal (setLocal l _t'3 (.Vint r)) _result
        (.Vint r)) _t'25 (.Vlong g)) _t'24 (.Vlong g)) _t'5 (.Vint r5)) _result (.Vint r5) :=
    lI_set_result (sub_setLocal (sub_setLocal (sub_setLocal hsub1 (by lI_ne)) (by lI_ne))
      (by lI_ne))
  -- if(result) return result;
  refine Sep.triple_seq ge _ _ _
    (LocalSt (envE c.bg c.bb)
      (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal l _t'3 (.Vint r)) _result
        (.Vint r)) _t'25 (.Vlong g)) _t'24 (.Vlong g)) _t'5 (.Vint r5)) _result (.Vint r5))
      (H c DB n' p' (.Vlong g))) _ _ _ ?_ ?_
  · exact ret_if_nz X _ n' p' _ r5 _ _ _ (mem_setLocal_head _ _ _) (fun _ _ _ _ h => h)
  -- data->req.headerbytecount += gotbytes; pp->nread_resp += gotbytes;
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (hbc_ok X _ n' p' g (hsub3 _ (by simp))) ?_
  refine triple_exists ge _ _ _ _ _ (fun v22 => ?_)
  refine Sep.triple_conseq ge _ _ (nr_ok X _ n' p' g (by tget (hsub3 _ (by simp))))
    (fun _ _ _ x => x) ?_
    (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
  intro e le hp ⟨v20, h⟩
  exact ⟨n', p', r5, g, hg, lst_weaken (sub_setLocal (sub_setLocal (sub_setLocal (sub_setLocal hsub3
    (by lI_ne)) (by lI_ne)) (by lI_ne)) (by lI_ne)) h⟩

/-! ## `ovfIf` 全体 -/

set_option maxHeartbeats 4000000 in
theorem ovf_ok (X : Ext c DB ge)
    (hPr : ∀ n p gv vs, SatisfiesAt ge (FunctionEntry2 ge) X.pread.fd (recvSpec c DB n p gv) vs)
    (l : List (Ident × Val)) (N : Nat) (hN : N ≤ 10) (r0 : Integers.Int) (n : Nat) (p : Val)
    (x : Integers.Int64) (B C : Sep.Assn)
    (hsub : ∀ q ∈ lI c (Integers.Int.repr (N : _root_.Int)) r0, q ∈ l)
    (h19 : (_t'19, Val.Vlong x) ∈ l) :
    Triple ge (FunctionEntry2 ge) f_Curl_pp_readresp
      (LocalSt (envE c.bg c.bb) l (H c DB n p vzero)) ovfIf (RetOK (J1 c DB N) B C) := by
  cases hx : Integers.Int64.eq x Integers.Int64.zero with
  | false =>
    -- overflow があるので読まない。gotbytes は 0 のまま
    refine triple_if_local ge _ _ _ _ _ _ false _ _ _
      (fun le m _ hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get h19))
        (notbool_long _ _), by rw [hx]; exact boolVal_ofBool_tint false m⟩) ?_
    exact Sep.triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x)
      (fun _ _ _ h => ⟨n, p, r0, _, Integers.Int64.repr 0,
        fun h0 => absurd h0 (by rw [zero_ne_900]; decide), lst_weaken hsub h⟩)
      (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
  | true =>
    refine triple_if_local ge _ _ _ _ _ _ true _ _ _
      (fun le m _ hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get h19))
        (notbool_long _ _), by rw [hx]; exact boolVal_ofBool_tint true m⟩) ?_
    have hml : (_maxloops, Val.Vint (Integers.Int.repr (N : _root_.Int))) ∈ l := hsub _ (by simp)
    -- t'2 = maxloops; maxloops = t'2 - 1;
    refine Sep.triple_seq ge _ _ _
      (fun e le hp => 1 ≤ N ∧ LocalSt (envE c.bg c.bb)
        (setLocal (setLocal l _t'2 (.Vint (Integers.Int.repr (N : _root_.Int)))) _maxloops
          (.Vint (Integers.Int.sub (Integers.Int.repr (N : _root_.Int)) (Integers.Int.repr 1))))
        (H c DB n p vzero) e le hp) _ _ _ ?_ ?_
    · refine triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ _ _ _ _t'2 _ _
            (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get hml)))
          (triple_set_local_fwd ge _ _ _ _ _ _maxloops _ _
            (fun le m hp hT _ _ => EvalExpr.Ebinop _ _ _ _ _ _ _
              (EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _)))
              (EvalExpr.Econst_int _ _) rfl))) ?_
      -- if(!t'2) return CURLE_OK;
      rcases Nat.eq_zero_or_pos N with rfl | hpos
      · refine triple_if_local ge _ _ _ _ _ _ true _ _ _
          (fun le m _ hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
            (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (notbool_int _ _),
            by rw [ml_zero]; exact boolVal_ofBool_tint true m⟩) ?_
        exact ret_val ge _ X.cenv c X.bgbb DB n p _ _ _ (.Vint (Integers.Int.repr 0)) _ _ _
          (fun _ _ _ => EvalExpr.Econst_int _ _) (fun _ => rfl)
      · refine triple_if_local ge _ _ _ _ _ _ false _ _ _
          (fun le m _ hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
            (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (notbool_int _ _),
            by rw [(ml_pos N hpos hN).1]; exact boolVal_ofBool_tint false m⟩) ?_
        exact Sep.triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x)
          (fun _ _ _ h => ⟨hpos, h⟩)
          (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
    -- 読む。maxloops は N - 1 になっている（N = 0 なら上で戻っている）
    refine triple_pure ge _ _ _ _ _ _ (fun hpos => ?_)
    have hsub2 := lI_set_ml (mx1 := Integers.Int.sub (Integers.Int.repr (N : _root_.Int))
      (Integers.Int.repr 1)) (sub_setLocal (id := _t'2) (v := .Vint (Integers.Int.repr (N : _root_.Int))) hsub
        (by lI_ne))
    refine Sep.triple_conseq ge _ _ (read_ok X hPr _ _ r0 n p vzero B C hsub2)
      (fun _ _ _ x => x) ?_ (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
    intro e le hp ⟨n', p', r, g, _, h⟩
    exact ⟨n', p', r, _, g, fun _ => ⟨N - 1, by omega, by omega, (ml_pos N hpos hN).2⟩, h⟩

end Case1C
