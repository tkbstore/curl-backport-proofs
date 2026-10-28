/-
Case 1: 修正後の `Curl_pp_readresp` の内側のループ（受信バッファの行を1つずつ取り出す）が止まること。

減少量は受信バッファの長さ `n`。1回まわるごとに、改行までの1行（1バイト以上）を
`curlx_dyn_tail` で取り除くか、`curlx_dyn_reset` で空にする。改行がなければ抜ける。
このループは修正の前後で同じである（修正は外側のループだけを変えた）。
-/
import Case1Arith
import Case1Stmts
open CC CC.Sep CC.HProp
open Case1_after
open Case5C (addr eval_field boolVal_ofBool_tint boolVal_ofBool_tbool)
open Case4C (IsPtr cast_ptr lv_field eval_deref_temp)

set_option maxRecDepth 20000

namespace Case1C

variable {ge : CGenv} {c : Ctx} {DB : Nat → Val → HProp}

abbrev tyPP : Ty := tptr (Ty.Tstruct _pingpong noattr)

/-- 外側のループをまたいで保つ一時変数。 -/
abbrev lI (c : Ctx) (mx r : Integers.Int) : List (Ident × Val) :=
  [(_data, .Vptr c.dataB c.dataO), (_sockindex, c.sockV), (_pp, .Vptr c.ppB c.ppO),
   (_code, .Vptr c.codeB c.codeO), (_size, .Vptr c.sizeB c.sizeO), (_conn, c.connV),
   (_maxloops, .Vint mx), (_result, .Vint r)]

/-- 内側のループの不変条件。`n` が受信バッファの長さ。 -/
def I2 (c : Ctx) (DB : Nat → Val → HProp) (mx : Integers.Int) (gv : Val) (n : Nat) : Sep.Assn :=
  fun e le hp => ∃ p r, LocalSt (envE c.bg c.bb) (lI c mx r) (H c DB n p gv) e le hp

def J2 (c : Ctx) (DB : Nat → Val → HProp) (mx : Integers.Int) (gv : Val) (n : Nat) : Sep.Assn :=
  fun e le hp => ∃ n', n' < n ∧ I2 c DB mx gv n' e le hp

/-- 内側のループを抜けたあと。`gotbytes` はそのままか、0 が書かれている。 -/
def Post2 (c : Ctx) (DB : Nat → Val → HProp) (mx : Integers.Int) (gv : Val) : Sep.Assn :=
  fun e le hp => ∃ n p r gv', (gv' = gv ∨ gv' = vzero)
    ∧ LocalSt (envE c.bg c.bb) (lI c mx r) (H c DB n p gv') e le hp

/-! ## 道具 -/

theorem lst_weaken {E : Env} {l l' : List (Ident × Val)} {Hh : HProp} {e : Env} {le : TempEnv}
    {hp : Heap} (hsub : ∀ q ∈ l', q ∈ l) (h : LocalSt E l Hh e le hp) : LocalSt E l' Hh e le hp :=
  ⟨h.1, TempsHold_mono hsub h.2.1, h.2.2⟩

theorem sub_setLocal {l l0 : List (Ident × Val)} {id : Ident} {v : Val}
    (hsub : ∀ q ∈ l0, q ∈ l) (hne : ∀ q ∈ l0, q.1 ≠ id) : ∀ q ∈ l0, q ∈ setLocal l id v :=
  fun q hq => mem_setLocal_of_mem (hsub q hq) (hne q hq)

/-- `lI` の識別子が `id` と違うこと。 -/
macro "lI_ne" : tactic =>
  `(tactic| (simp only [lI, List.forall_mem_cons, List.forall_mem_nil, and_true]; decide))

theorem db_part {n : Nat} {p gv : Val} {hp : Heap} (hH : H c DB n p gv hp) :
    ∃ h, DB n p h ∧ Sub h hp := by
  obtain ⟨_, _, hd, rfl, _, hR⟩ := hH
  obtain ⟨_, hdb, hd2, rfl, _, hD⟩ := hR
  exact ⟨hdb, hD, sub_trans (sub_right hd2) (sub_right hd)⟩

/-- 受信バッファの述語から分かる純粋な事実を、先に取り出す。 -/
theorem with_db (X : Ext c DB ge) {fe f} {l : List (Ident × Val)} {n : Nat} {p gv : Val}
    {s : Stmt} {R : Sep.ExitConds}
    (h : IsPtr p → n < 2 ^ 64 → Triple ge fe f (LocalSt (envE c.bg c.bb) l (H c DB n p gv)) s R) :
    Triple ge fe f (LocalSt (envE c.bg c.bb) l (H c DB n p gv)) s R := by
  intro k e le hp hf m hd hag hP
  obtain ⟨_, hD, _⟩ := db_part hP.2.2
  exact h (X.dbPtr _ _ _ hD) (X.dbSize _ _ _ hD) k e le hp hf m hd hag hP

theorem ev_callee {id : Ident} {tyargs : List Ty} {tyres : Ty} {cc : CallConv}
    (C : Callee ge id tyargs tyres cc) {le : TempEnv} {m : Mem}
    (hloc : (envE c.bg c.bb).get id = none) :
    EvalExpr ge (envE c.bg c.bb) le m (.Evar id (.Tfunction tyargs tyres cc))
      (.Vptr C.b Integers.Ptrofs.zero) :=
  eval_callee_global hloc C.sym rfl

/-- `&pp->recvbuf` -/
theorem ev_rb (X : Ext c DB ge) {le : TempEnv} {m : Mem}
    (hpp : le.get _pp = some (.Vptr c.ppB c.ppO)) :
    EvalExpr ge (envE c.bg c.bb) le m
      (.Eaddrof (.Efield (.Ederef (.Etempvar _pp tyPP) (.Tstruct _pingpong noattr)) _recvbuf
        (.Tstruct _dynbuf noattr)) tyDyn) (rbV c) :=
  EvalExpr.Eaddrof _ _ _ _ (lv_field (eval_deref_temp hpp) rfl (by rw [X.cenv]; exact co_pp)
    (by rw [X.cenv]; exact off_recvbuf))

theorem args_rb (X : Ext c DB ge) {le : TempEnv} {m : Mem}
    (hpp : le.get _pp = some (.Vptr c.ppB c.ppO)) :
    EvalExprlist ge (envE c.bg c.bb) le m
      [.Eaddrof (.Efield (.Ederef (.Etempvar _pp tyPP) (.Tstruct _pingpong noattr)) _recvbuf
        (.Tstruct _dynbuf noattr)) tyDyn] [tyDyn] [rbV c] :=
  .cons _ _ _ _ _ _ _ (ev_rb X hpp) rfl .nil

/-- 呼び出しのあとに文が続く形。戻り値は `φ` を満たす何か。 -/
theorem call_some_then {fe f} (S : FunSpec) (id : Ident) (a : Expr) (al : List Expr)
    (E : Env) (l : List (Ident × Val)) (Hh : HProp) (vargs : List Val) (fb : Block) (fd : FunDef)
    (φ : Val → Prop) (Q : Val → HProp) (s2 : Stmt) (R : Sep.ExitConds)
    (hspec : ∀ vs, SatisfiesAt ge fe fd S vs) (hfind : FuncPtr ge fb fd)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun (typeof a) = .f S.tyargs S.tyres S.cc)
    (hcallee : ∀ le m, TempsHold l le → EvalExpr ge E le m a (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge E le m al S.tyargs vargs)
    (hpre : ∀ h, Hh h → S.pre vargs h)
    (hpost : ∀ v h, S.post v h → φ v ∧ Q v h)
    (hnext : ∀ v, φ v → Triple ge fe f (LocalSt E (setLocal l id v) (Q v)) s2 R) :
    Triple ge fe f (LocalSt E l Hh) (.Ssequence (.Scall (some id) a al) s2) R :=
  seq_ex ge fe f _ _ R _ s2
    (call_some ge fe f S id a al E l Hh vargs fb fd φ Q hspec hfind hty hclass hcallee hargs
      hpre hpost)
    (fun v => triple_pure ge fe f _ _ s2 R (hnext v))

theorem call_none_then {fe f} (S : FunSpec) (a : Expr) (al : List Expr)
    (E : Env) (l : List (Ident × Val)) (Hh : HProp) (vargs : List Val) (fb : Block) (fd : FunDef)
    (φ : Val → Prop) (Q : Val → HProp) (s2 : Stmt) (R : Sep.ExitConds)
    (hspec : ∀ vs, SatisfiesAt ge fe fd S vs) (hfind : FuncPtr ge fb fd)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun (typeof a) = .f S.tyargs S.tyres S.cc)
    (hcallee : ∀ le m, TempsHold l le → EvalExpr ge E le m a (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge E le m al S.tyargs vargs)
    (hpre : ∀ h, Hh h → S.pre vargs h)
    (hpost : ∀ v h, S.post v h → φ v ∧ Q v h)
    (hnext : ∀ v, φ v → Triple ge fe f (LocalSt E l (Q v)) s2 R) :
    Triple ge fe f (LocalSt E l Hh) (.Ssequence (.Scall none a al) s2) R :=
  seq_ex ge fe f _ _ R _ s2
    (call_none ge fe f S a al E l Hh vargs fb fd φ Q hspec hfind hty hclass hcallee hargs
      hpre hpost)
    (fun v => triple_pure ge fe f _ _ s2 R (hnext v))

/-- 最後の文が呼び出しで、結果は使わない形。 -/
theorem call_none_last {fe f} (S : FunSpec) (a : Expr) (al : List Expr)
    (E : Env) (l : List (Ident × Val)) (Hh : HProp) (vargs : List Val) (fb : Block) (fd : FunDef)
    (Q : HProp) (R : Sep.ExitConds)
    (hspec : ∀ vs, SatisfiesAt ge fe fd S vs) (hfind : FuncPtr ge fb fd)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun (typeof a) = .f S.tyargs S.tyres S.cc)
    (hcallee : ∀ le m, TempsHold l le → EvalExpr ge E le m a (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge E le m al S.tyargs vargs)
    (hpre : ∀ h, Hh h → S.pre vargs h)
    (hpost : ∀ v h, S.post v h → Q h)
    (hend : ∀ e le hp, LocalSt E l Q e le hp → R.normal e le hp) :
    Triple ge fe f (LocalSt E l Hh) (.Scall none a al) R :=
  Sep.triple_conseq ge fe f
    (call_none ge fe f S a al E l Hh vargs fb fd (fun _ => True) (fun _ => Q) hspec hfind hty
      hclass hcallee hargs hpre (fun v h hs => ⟨trivial, hpost v h hs⟩))
    (fun _ _ _ x => x) (fun e le hp ⟨_, _, hL⟩ => hend e le hp hL)
    (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)

/-! ## 受信バッファを詰める部分（`tailStmt`）

```c
if(curlx_dyn_len(&pp->recvbuf) > length)
  curlx_dyn_tail((&pp->recvbuf), curlx_dyn_len(&pp->recvbuf) - length);
else
  curlx_dyn_reset(&pp->recvbuf);
```
-/

theorem ev_gt {le : TempEnv} {m : Mem} {E : Env} {t : Ident} {x y : Integers.Int64}
    (h1 : le.get t = some (.Vlong x)) (h2 : le.get _length = some (.Vlong y)) :
    EvalExpr ge E le m (.Ebinop .Ogt (.Etempvar t tulong) (.Etempvar _length tulong) tint)
      (Val.ofBool (Integers.Int64.cmpu .Cgt x y)) :=
  EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ h1) (EvalExpr.Etempvar _ _ _ h2) rfl

theorem tail_ok (X : Ext c DB ge) (l : List (Ident × Val)) (mx r : Integers.Int) (n : Nat)
    (p gv : Val) (L : Integers.Int64) (B C : Sep.Assn)
    (hsub : ∀ q ∈ lI c mx r, q ∈ l) (hlen : (_length, Val.Vlong L) ∈ l)
    (hL1 : 1 ≤ Integers.Int64.unsigned L) (hLn : Integers.Int64.unsigned L ≤ n) :
    Triple ge (FunctionEntry2 ge) f_Curl_pp_readresp
      (LocalSt (envE c.bg c.bb) l (H c DB n p gv)) tailStmt
      (RetOK (J2 c DB mx gv n) B C) := by
  refine with_db X (fun _ hn => ?_)
  have hpp : (_pp, Val.Vptr c.ppB c.ppO) ∈ l := hsub _ (by simp)
  refine call_some_then (lenSpec c DB n p gv) _t'15 _ _ _ l _ [rbV c] X.len.b X.len.fd
    (fun v => v = .Vlong (Integers.Int64.repr n)) (fun _ => H c DB n p gv) _ _
    (X.sLen n p gv) X.len.fp X.len.ty rfl (fun le m _ => ev_callee X.len rfl)
    (fun le m hT => args_rb X (hT.get hpp)) (fun h hH => ⟨rfl, hH⟩) (fun v h hs => hs)
    (fun v hv => ?_)
  subst hv
  have hlen' : (_length, Val.Vlong L) ∈ setLocal l _t'15 (.Vlong (Integers.Int64.repr n)) :=
    mem_setLocal_of_mem' hlen (by decide)
  have hpp' : (_pp, Val.Vptr c.ppB c.ppO) ∈ setLocal l _t'15 (.Vlong (Integers.Int64.repr n)) :=
    mem_setLocal_of_mem' hpp (by decide)
  cases hgt : Integers.Int64.cmpu .Cgt (Integers.Int64.repr n) L with
  | false =>
    refine triple_if_local ge _ _ _ _ _ _ false _ _ _
      (fun le m _ hT _ _ => ⟨_, ev_gt (hT.get (mem_setLocal_head _ _ _)) (hT.get hlen'),
        by rw [hgt]; exact boolVal_ofBool_tint false m⟩) ?_
    have h0 : 0 < n := by
      have h3 : (0 : _root_.Int) < (n : _root_.Int) :=
        Int.lt_of_lt_of_le (Int.lt_of_lt_of_le (by decide) hL1) hLn
      exact_mod_cast h3
    refine call_none_last (resetSpec c DB n p gv) _ _ _ _ _ [rbV c] X.reset.b X.reset.fd
      (fun h => ∃ p', H c DB 0 p' gv h) _ (X.sReset n p gv) X.reset.fp X.reset.ty rfl
      (fun le m _ => ev_callee X.reset rfl) (fun le m hT => args_rb X (hT.get hpp'))
      (fun h hH => ⟨rfl, hH⟩) (fun v h hs => hs) (fun e le hp hL => ?_)
    obtain ⟨he, hT, p', hH'⟩ := hL
    exact ⟨0, h0, p', r, lst_weaken (sub_setLocal hsub (by lI_ne)) ⟨he, hT, hH'⟩⟩
  | true =>
    refine triple_if_local ge _ _ _ _ _ _ true _ _ _
      (fun le m _ hT _ _ => ⟨_, ev_gt (hT.get (mem_setLocal_head _ _ _)) (hT.get hlen'),
        by rw [hgt]; exact boolVal_ofBool_tint true m⟩) ?_
    have hlt := tail_lt n L hn hL1 hgt
    refine call_some_then (lenSpec c DB n p gv) _t'14 _ _ _ _ _ [rbV c] X.len.b X.len.fd
      (fun v => v = .Vlong (Integers.Int64.repr n)) (fun _ => H c DB n p gv) _ _
      (X.sLen n p gv) X.len.fp X.len.ty rfl (fun le m _ => ev_callee X.len rfl)
      (fun le m hT => args_rb X (hT.get hpp')) (fun h hH => ⟨rfl, hH⟩) (fun v h hs => hs)
      (fun v hv => ?_)
    subst hv
    refine call_none_last (tailSpec c DB n p gv (Integers.Int64.sub (Integers.Int64.repr n) L))
      _ _ _ _ _ [rbV c, .Vlong (Integers.Int64.sub (Integers.Int64.repr n) L)]
      X.tail.b X.tail.fd
      (fun h => ∃ p', H c DB (tailLen n (Integers.Int64.sub (Integers.Int64.repr n) L)) p' gv h) _
      (X.sTail n p gv _) X.tail.fp X.tail.ty rfl (fun le m _ => ev_callee X.tail rfl)
      (fun le m hT => .cons _ _ _ _ _ _ _ (ev_rb X (hT.get (mem_setLocal_of_mem' hpp' (by decide))))
        rfl (.cons _ _ _ _ _ _ _
          (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _)))
            (EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_of_mem' hlen' (by decide)))) rfl)
          rfl .nil))
      (fun h hH => ⟨rfl, hH⟩) (fun v h hs => hs.2) (fun e le hp hL => ?_)
    obtain ⟨he, hT, p', hH'⟩ := hL
    exact ⟨_, hlt, p', r, lst_weaken (sub_setLocal (sub_setLocal hsub (by lI_ne)) (by lI_ne))
      ⟨he, hT, hH'⟩⟩

/-! ## 応答の終わりの行に当たったとき（`eorIf`）

```c
if(pp->endofresp(data, conn, line, length, code)) {
  pp->nfinal = length;
  if(curlx_dyn_len(&pp->recvbuf) > length)
    pp->overflow = curlx_dyn_len(&pp->recvbuf) - length;
  else
    pp->overflow = 0;
  *size = pp->nread_resp;
  pp->nread_resp = 0;
  gotbytes = 0;
  break;
}
```
-/

/-- 一時変数への代入で、値は `P` を満たす何か。 -/
theorem set_any {fe f} (E : Env) (l : List (Ident × Val)) (Hh : HProp) (id : Ident) (a : Expr)
    (P : Val → Prop)
    (hev : ∀ le m hp, TempsHold l le → Hh hp → Heap.Agrees hp m →
      ∃ v, P v ∧ EvalExpr ge E le m a v) :
    Triple ge fe f (LocalSt E l Hh) (.Sset id a)
      (.only (fun e le hp => ∃ v, P v ∧ LocalSt E (setLocal l id v) Hh e le hp)) := by
  refine Sep.triple_conseq ge fe f
    (triple_set ge fe f (LocalSt E l Hh) _ id a (fun e le hp m hP hag => ?_))
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  obtain ⟨v, hPv, hv⟩ := hev le m hp hT hH hag
  exact ⟨v, hv, v, hPv, rfl,
    TempsHold_set (fun _ hq => (mem_dropId hq).2) (TempsHold_mono (fun _ hq => (mem_dropId hq).1) hT),
    hH⟩

/-- `pp->fld`（`fld` は `IsLong` のセル）を読む。 -/
theorem ev_ppfield (X : Ext c DB ge) {n : Nat} {p gv : Val} {k : Nat}
    {hk : k < (cells c).length} {d : Z} {fld : Ident} {le : TempEnv} {m : Mem} {hp : Heap}
    (hcell : (cells c)[k]'hk = cellP .Mint64 c.pm c.ppB (addr c.ppO d) IsLong)
    (hfld : fieldOffset prog.prog_comp_env fld (coOf _pingpong).co_members = .OK (d, .Full))
    (hpp : le.get _pp = some (.Vptr c.ppB c.ppO)) (hH : H c DB n p gv hp)
    (hag : Heap.Agrees hp m) :
    ∃ v, IsLong v ∧ EvalExpr ge (envE c.bg c.bb) le m
      (.Efield (.Ederef (.Etempvar _pp tyPP) (.Tstruct _pingpong noattr)) fld tulong) v := by
  obtain ⟨v, ⟨x, rfl⟩, hload⟩ := cell_load hcell X.pmR hH hag
  exact ⟨_, ⟨x, rfl⟩, eval_field hpp (by rw [X.cenv]; exact co_pp) (by rw [X.cenv]; exact hfld)
    rfl hload⟩

theorem lv_pp (X : Ext c DB ge) {d : Z} {fld : Ident} {ty : Ty} {le : TempEnv} {m : Mem}
    (hfld : fieldOffset prog.prog_comp_env fld (coOf _pingpong).co_members = .OK (d, .Full))
    (hpp : le.get _pp = some (.Vptr c.ppB c.ppO)) :
    EvalLvalue ge (envE c.bg c.bb) le m
      (.Efield (.Ederef (.Etempvar _pp tyPP) (.Tstruct _pingpong noattr)) fld ty) c.ppB
      (Integers.Ptrofs.add c.ppO (Integers.Ptrofs.repr d)) .Full :=
  lv_field (eval_deref_temp hpp) rfl (by rw [X.cenv]; exact co_pp) (by rw [X.cenv]; exact hfld)

/-- 抜けるときの一時変数（`length` と `lI`）。 -/
abbrev l0 (c : Ctx) (mx r : Integers.Int) (L : Integers.Int64) : List (Ident × Val) :=
  (_length, .Vlong L) :: lI c mx r

theorem eor_ok (X : Ext c DB ge) (l : List (Ident × Val)) (mx r : Integers.Int) (n : Nat)
    (p gv : Val) (L : Integers.Int64) (b : Bool) (C : Sep.Assn)
    (hsub : ∀ q ∈ lI c mx r, q ∈ l) (hlen : (_length, Val.Vlong L) ∈ l)
    (h13 : (_t'13, Val.ofBool b) ∈ l) :
    Triple ge (FunctionEntry2 ge) f_Curl_pp_readresp
      (LocalSt (envE c.bg c.bb) l (H c DB n p gv)) eorIf
      (RetOK (LocalSt (envE c.bg c.bb) l (H c DB n p gv)) (Post2 c DB mx gv) C) := by
  refine triple_if_local ge _ _ _ _ _ _ b _ _ _
    (fun le m _ hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get h13), boolVal_ofBool_tbool b m⟩) ?_
  cases b with
  | false =>
    exact Sep.triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
  | true =>
  -- 一時変数を l0 に絞る
  refine Sep.triple_pre ge _ _
    (P := LocalSt (envE c.bg c.bb) (l0 c mx r L) (H c DB n p gv))
    (fun _ _ _ h => lst_weaken (fun q hq => by
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hlen
      · exact hsub q hq) h) ?_
  -- pp->nfinal = length;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (assign_cell ge _ _ c DB n p gv _ _ 7 (by simp [cells]) .Mint64 c.pm c.ppB
      (Integers.Ptrofs.add c.ppO (Integers.Ptrofs.repr 32)) IsLong rfl _ _ X.pmW rfl
      (fun le m hT => lv_pp X off_nfinal (hT.get (by temps_get)))
      (fun le m hp hT _ _ => ⟨_, _, EvalExpr.Etempvar _ _ (.Vlong L) (hT.get (by temps_get)), rfl,
        ⟨L, rfl⟩⟩))
    ?_
  -- if(curlx_dyn_len(..) > length) pp->overflow = ...; else pp->overflow = 0;
  refine triple_seq_fwd ge _ _ _ (LocalSt (envE c.bg c.bb) (l0 c mx r L) (H c DB n p gv)) _ _ _
    ?_ ?_
  · refine call_some_then (lenSpec c DB n p gv) _t'12 _ _ _ _ _ [rbV c] X.len.b X.len.fd
      (fun v => v = .Vlong (Integers.Int64.repr n)) (fun _ => H c DB n p gv) _ _
      (X.sLen n p gv) X.len.fp X.len.ty rfl (fun le m _ => ev_callee X.len rfl)
      (fun le m hT => args_rb X (hT.get (by temps_get))) (fun h hH => ⟨rfl, hH⟩)
      (fun v h hs => hs) (fun v hv => ?_)
    subst hv
    cases hgt : Integers.Int64.cmpu .Cgt (Integers.Int64.repr n) L with
    | false =>
      refine triple_if_local ge _ _ _ _ _ _ false _ _ _
        (fun le m _ hT _ _ => ⟨_, ev_gt (x := Integers.Int64.repr n) (y := L)
          (hT.get (by temps_get)) (hT.get (by temps_get)),
          by rw [hgt]; exact boolVal_ofBool_tint false m⟩) ?_
      refine Sep.triple_conseq ge _ _
        (assign_cell ge _ _ c DB n p gv _ _ 6 (by simp [cells]) .Mint64 c.pm c.ppB
          (Integers.Ptrofs.add c.ppO (Integers.Ptrofs.repr 24)) IsLong rfl _ _ X.pmW rfl
          (fun le m hT => lv_pp X off_overflow (hT.get (by temps_get)))
          (fun le m hp hT _ _ => ⟨_, _, EvalExpr.Econst_int _ _, rfl, ⟨_, rfl⟩⟩))
        (fun _ _ _ x => x) (fun _ _ _ h => lst_weaken (sub_setLocal (fun _ x => x) (by lI_ne)) h)
        (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
    | true =>
      refine triple_if_local ge _ _ _ _ _ _ true _ _ _
        (fun le m _ hT _ _ => ⟨_, ev_gt (x := Integers.Int64.repr n) (y := L)
          (hT.get (by temps_get)) (hT.get (by temps_get)),
          by rw [hgt]; exact boolVal_ofBool_tint true m⟩) ?_
      refine call_some_then (lenSpec c DB n p gv) _t'11 _ _ _ _ _ [rbV c] X.len.b X.len.fd
        (fun v => v = .Vlong (Integers.Int64.repr n)) (fun _ => H c DB n p gv) _ _
        (X.sLen n p gv) X.len.fp X.len.ty rfl (fun le m _ => ev_callee X.len rfl)
        (fun le m hT => args_rb X (hT.get (by temps_get))) (fun h hH => ⟨rfl, hH⟩)
        (fun v h hs => hs) (fun v hv => ?_)
      subst hv
      refine Sep.triple_conseq ge _ _
        (assign_cell ge _ _ c DB n p gv _ _ 6 (by simp [cells]) .Mint64 c.pm c.ppB
          (Integers.Ptrofs.add c.ppO (Integers.Ptrofs.repr 24)) IsLong rfl _ _ X.pmW rfl
          (fun le m hT => lv_pp X off_overflow (hT.get (by temps_get)))
          (fun le m hp hT _ _ => ⟨_, _, EvalExpr.Ebinop _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ (.Vlong (Integers.Int64.repr n)) (hT.get (by temps_get)))
            (EvalExpr.Etempvar _ _ (.Vlong L) (hT.get (by temps_get))) rfl, rfl, ⟨_, rfl⟩⟩))
        (fun _ _ _ x => x)
        (fun _ _ _ h => lst_weaken (sub_setLocal (sub_setLocal (fun _ x => x) (by lI_ne))
          (by lI_ne)) h)
        (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
  -- *size = pp->nread_resp;
  refine Sep.triple_seq ge _ _ _
    (fun e le hp => ∃ v, IsLong v ∧ LocalSt (envE c.bg c.bb) (setLocal (l0 c mx r L) _t'17 v)
      (H c DB n p gv) e le hp) _ _ _ ?_ ?_
  · refine triple_seq_fwd ge _ _ _ _ _ _ _
      (set_any _ _ _ _t'17 _ IsLong (fun le m hp hT hH hag =>
        ev_ppfield X (k := 5) (hk := by simp [cells]) rfl off_nread (hT.get (by temps_get)) hH hag)) ?_
    refine triple_exists ge _ _ _ _ _ (fun v => ?_)
    refine triple_pure ge _ _ _ _ _ _ (fun hv => ?_)
    obtain ⟨x, rfl⟩ := hv
    refine triple_weaken_only ge _ _ ?_
    refine Sep.triple_conseq ge _ _
      (assign_cell ge _ _ c DB n p gv _ _ 2 (by simp [cells]) .Mint64 c.pm c.sizeB c.sizeO AnyV rfl
        _ _ X.pmW rfl
        (fun le m hT => EvalLvalue.Ederef _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))
        (fun le m hp hT _ _ => ⟨_, _, EvalExpr.Etempvar _ _ (.Vlong x) (hT.get (by temps_get)), rfl,
          trivial⟩))
      (fun _ _ _ x => x) (fun _ _ _ h => ⟨_, ⟨x, rfl⟩, h⟩)
      (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
  refine triple_exists ge _ _ _ _ _ (fun v => ?_)
  refine triple_pure ge _ _ _ _ _ _ (fun _ => ?_)
  -- pp->nread_resp = 0;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (assign_cell ge _ _ c DB n p gv _ _ 5 (by simp [cells]) .Mint64 c.pm c.ppB
      (Integers.Ptrofs.add c.ppO (Integers.Ptrofs.repr 0)) IsLong rfl _ _ X.pmW rfl
      (fun le m hT => lv_pp X off_nread (hT.get (by temps_get)))
      (fun le m hp hT _ _ => ⟨_, _, EvalExpr.Econst_int _ _, rfl, ⟨_, rfl⟩⟩)) ?_
  -- gotbytes = 0;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (assign_got ge _ _ c DB n p gv _ _ (envE_got c.bg c.bb) _ vzero
      (fun le m _ => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)) ?_
  -- break;
  exact Sep.triple_conseq ge _ _ (triple_break ge _ _ _) (fun _ _ _ x => x)
    (fun _ _ _ x => False.elim x)
    (fun _ _ _ h => ⟨n, p, r, vzero, Or.inr rfl,
      lst_weaken (sub_setLocal (fun _ hq => List.mem_cons_of_mem _ hq) (by lI_ne)) h⟩)
    (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)

/-! ## 改行が見つかったか（`nlIf`） -/

theorem sem_sub_ptr (cenv : CompositeEnv) (m : Mem) (bl : Block) (ol : Integers.Ptrofs) (i : Nat) :
    Cop.semBinaryOperation cenv .Osub (.Vptr bl (Integers.Ptrofs.add ol (Integers.Ptrofs.repr i)))
      (tptr tschar) (.Vptr bl ol) (tptr tschar) m
    = some (Val.Vptrofs (Integers.MI.divs
        (Integers.Ptrofs.sub (Integers.Ptrofs.add ol (Integers.Ptrofs.repr i)) ol)
        (Integers.Ptrofs.repr 1))) := by
  have hc : Cop.classifySub (tptr tschar) (tptr tschar) = .pp tschar := rfl
  have hs : sizeof cenv tschar = 1 := rfl
  simp only [Cop.semBinaryOperation, Cop.semSub, hc, hs]
  simp
  decide

/-- `length = nl - line + 1;` の値。 -/
theorem ev_length {le : TempEnv} {m : Mem} {E : Env} {bl : Block} {ol : Integers.Ptrofs} {i : Nat}
    (h1 : le.get _nl = some (.Vptr bl (Integers.Ptrofs.add ol (Integers.Ptrofs.repr i))))
    (h2 : le.get _line = some (.Vptr bl ol)) :
    EvalExpr ge E le m
      (.Ebinop .Oadd (.Ebinop .Osub (.Etempvar _nl (tptr tschar)) (.Etempvar _line (tptr tschar)) tlong)
        (.Econst_int (Integers.Int.repr 1) tint) tlong)
      (.Vlong (Integers.Int64.repr ((i : _root_.Int) + 1))) := by
  rw [← lenv ol i]
  exact EvalExpr.Ebinop _ _ _ _ _ _ _
    (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ h1) (EvalExpr.Etempvar _ _ _ h2)
      (sem_sub_ptr _ _ _ _ _))
    (EvalExpr.Econst_int _ _) rfl

theorem boolVal_ptr {m : Mem} {b : Block} {o : Integers.Ptrofs} (t : Ty)
    (h : Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) :
    Cop.boolVal (.Vptr b o) (tptr t) m = some true := by
  have hc : Cop.classifyBool (tptr t) = .l := rfl
  simp [Cop.boolVal, hc, h, Archi.ptr64]

theorem boolVal_null (t : Ty) (m : Mem) :
    Cop.boolVal (.Vlong Integers.Int64.zero) (tptr t) m = some false := rfl

/-- `memchr` が返した位置が、受信バッファの中で有効であること。 -/
theorem valid_at (X : Ext c DB ge) {n : Nat} {gv : Val} {bl : Block} {ol : Integers.Ptrofs}
    {i : Nat} {hp : Heap} {m : Mem} (hH : H c DB n (.Vptr bl ol) gv hp) (hag : Heap.Agrees hp m)
    (hi : i < n) :
    Mem.weakValidPointer m bl
      (Integers.Ptrofs.unsigned (Integers.Ptrofs.add ol (Integers.Ptrofs.repr i))) = true := by
  obtain ⟨h, hD, hs⟩ := db_part hH
  exact X.dbValid n bl ol h m i hD (agrees_sub hs hag) hi

/-- `result` を書き換えたあとも、`lI` の他の一時変数は残る。 -/
theorem lI_set_result {l : List (Ident × Val)} {mx r r1 : Integers.Int}
    (hsub : ∀ q ∈ lI c mx r, q ∈ l) : ∀ q ∈ lI c mx r1, q ∈ setLocal l _result (.Vint r1) := by
  intro q hq
  simp only [lI, List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact mem_setLocal_of_mem' (hsub _ (by simp)) (by decide)
  · exact mem_setLocal_of_mem' (hsub _ (by simp)) (by decide)
  · exact mem_setLocal_of_mem' (hsub _ (by simp)) (by decide)
  · exact mem_setLocal_of_mem' (hsub _ (by simp)) (by decide)
  · exact mem_setLocal_of_mem' (hsub _ (by simp)) (by decide)
  · exact mem_setLocal_of_mem' (hsub _ (by simp)) (by decide)
  · exact mem_setLocal_of_mem' (hsub _ (by simp)) (by decide)
  · exact mem_setLocal_head _ _ _

set_option maxHeartbeats 4000000 in
theorem nl_ok (X : Ext c DB ge) (l : List (Ident × Val)) (mx r : Integers.Int) (n : Nat)
    (p gv v8 : Val)
    (hsub : ∀ q ∈ lI c mx r, q ∈ l) (hline : (_line, p) ∈ l) (hnl : (_nl, v8) ∈ l)
    (hin : InRange p (Integers.Int64.repr n) v8) :
    Triple ge (FunctionEntry2 ge) f_Curl_pp_readresp
      (LocalSt (envE c.bg c.bb) l (H c DB n p gv)) nlIf
      (RetOK (J2 c DB mx gv n) (Post2 c DB mx gv) (J2 c DB mx gv n)) := by
  refine with_db X (fun hptr hn => ?_)
  have hpp : (_pp, Val.Vptr c.ppB c.ppO) ∈ l := hsub _ (by simp)
  have hdata : (_data, Val.Vptr c.dataB c.dataO) ∈ l := hsub _ (by simp)
  rcases hin with rfl | ⟨bl, ol, i, rfl, hi, rfl⟩
  · -- 改行がない: pp->overflow = 0; break;
    refine triple_if_local ge _ _ _ _ _ _ false _ _ _
      (fun le m _ hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get hnl), boolVal_null _ m⟩) ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (assign_cell ge _ _ c DB n p gv _ _ 6 (by simp [cells]) .Mint64 c.pm c.ppB
        (Integers.Ptrofs.add c.ppO (Integers.Ptrofs.repr 24)) IsLong rfl _ _ X.pmW rfl
        (fun le m hT => lv_pp X off_overflow (hT.get hpp))
        (fun le m hp hT _ _ => ⟨_, _, EvalExpr.Econst_int _ _, rfl, ⟨_, rfl⟩⟩)) ?_
    exact Sep.triple_conseq ge _ _ (triple_break ge _ _ _) (fun _ _ _ x => x)
      (fun _ _ _ x => False.elim x)
      (fun _ _ _ h => ⟨n, p, r, gv, Or.inl rfl, lst_weaken hsub h⟩)
      (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
  · -- 改行がある
    have hin : i < n := by
      have := uns_repr n hn
      have h' : (i : _root_.Int) < Integers.Int64.unsigned (Integers.Int64.repr n) := hi
      rw [this] at h'
      exact_mod_cast h'
    refine triple_if_local ge _ _ _ _ _ _ true _ _ _
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get hnl),
        boolVal_ptr _ (valid_at X hH hag hin)⟩) ?_
    -- length = nl - line + 1;
    have hL : Integers.Int64.unsigned (Integers.Int64.repr ((i : _root_.Int) + 1)) = (i : _root_.Int) + 1 := by
      have := uns_repr (i + 1) (by omega)
      simpa using this
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ _ _ _ _length _ (.Vlong (Integers.Int64.repr ((i : _root_.Int) + 1)))
        (fun le m hp hT _ _ => ev_length (hT.get hnl) (hT.get hline))) ?_
    -- 以下 L = length の値
    generalize hLdef : Integers.Int64.repr ((i : _root_.Int) + 1) = L at hL ⊢
    have hL1 : 1 ≤ Integers.Int64.unsigned L := by
      have : (1 : _root_.Int) ≤ (i : _root_.Int) + 1 := by omega
      rw [hL]; exact this
    have hLn : Integers.Int64.unsigned L ≤ n := by
      have : (i : _root_.Int) + 1 ≤ (n : _root_.Int) := by omega
      rw [hL]; exact this
    have hcode : (_code, Val.Vptr c.codeB c.codeO) ∈ l := hsub _ (by simp)
    have hconn : (_conn, c.connV) ∈ l := hsub _ (by simp)
    have hdataPtr : ∀ m, Cop.semCast (.Vptr c.dataB c.dataO) tyEasy tyEasy m
        = some (.Vptr c.dataB c.dataO) := fun _ => rfl
    have hlineC : ∀ m t, Cop.semCast (.Vptr bl ol) (tptr tschar) (tptr t) m = some (.Vptr bl ol) :=
      fun _ _ => rfl
    -- t'9 = memchr(line, 0, length); if(t'9) { failf(...); return CURLE_WEIRD_SERVER_REPLY; }
    refine Sep.triple_seq ge _ _ _
      (fun e le hp => ∃ v9, LocalSt (envE c.bg c.bb)
        (setLocal (setLocal l _length (.Vlong L)) _t'9 v9) (H c DB n (.Vptr bl ol) gv) e le hp)
      _ _ _ ?_ ?_
    · refine call_some_then (memchrSpec c DB n (.Vptr bl ol) gv L (Integers.Int.repr 0)) _t'9 _ _ _ _ _
        [.Vptr bl ol, .Vint (Integers.Int.repr 0), .Vlong L] X.memchr.b X.memchr.fd
        (InRange (.Vptr bl ol) L) (fun _ => H c DB n (.Vptr bl ol) gv) _ _
        (X.sMemchr n _ gv L _) X.memchr.fp X.memchr.ty rfl (fun le m _ => ev_callee X.memchr rfl)
        (fun le m hT => .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
          (hlineC m _) (.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl
          (.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _))) rfl .nil)))
        (fun h hH => ⟨rfl, hLn, hH⟩) (fun v h hs => hs) (fun v9 hin9 => ?_)
      rcases hin9 with rfl | ⟨bl', ol', j, hpe, hj, rfl⟩
      · refine triple_if_local ge _ _ _ _ _ _ false _ _ _
          (fun le m _ hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _)),
            boolVal_null _ m⟩) ?_
        exact Sep.triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x)
          (fun _ _ _ h => ⟨_, h⟩) (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x)
          (fun _ _ x => False.elim x)
      · cases hpe
        have hjn : j < n := by
          have h' : (j : _root_.Int) < Integers.Int64.unsigned L := hj
          have h2 : Integers.Int64.unsigned L ≤ (n : _root_.Int) := hLn
          have h3 : (j : _root_.Int) < (n : _root_.Int) := Int.lt_of_lt_of_le h' h2
          exact_mod_cast h3
        refine triple_if_local ge _ _ _ _ _ _ true _ _ _
          (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _)),
            boolVal_ptr _ (valid_at X hH hag hjn)⟩) ?_
        refine call_none_then (failfSpec c DB n (.Vptr bl ol) gv X.lit) _ _ _ _ _
          [.Vptr c.dataB c.dataO, .Vptr X.lit Integers.Ptrofs.zero] X.failf.b X.failf.fd
          (fun _ => True) (fun _ => H c DB n (.Vptr bl ol) gv) _ _
          (X.sFailf n _ gv) X.failf.fp X.failf.ty rfl (fun le m _ => ev_callee X.failf rfl)
          (fun le m hT => .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
            (hdataPtr m) (.cons _ _ _ _ _ _ _
              (EvalExpr.Elvalue _ _ _ _ _ (EvalLvalue.Evar_global _ _ _ (envE_lit c.bg c.bb) X.lit_sym)
                (DerefLoc.reference rfl)) rfl .nil))
          (fun h hH => ⟨rfl, hH⟩) (fun v h hs => ⟨trivial, hs⟩) (fun _ _ => ?_)
        exact ret_val ge _ X.cenv c X.bgbb DB n _ gv _ _ (.Vint (Integers.Int.repr 8)) _ _ _
          (fun _ _ _ => EvalExpr.Econst_int _ _) (fun _ => rfl)
    refine triple_exists ge _ _ _ _ _ (fun v9 => ?_)
    -- Curl_debug(data, CURLINFO_HEADER_IN, line, length);
    refine call_none_then (debugSpec c DB n (.Vptr bl ol) gv L) _ _ _ _ _
      [.Vptr c.dataB c.dataO, .Vint (Integers.Int.repr 1), .Vptr bl ol, .Vlong L]
      X.debug.b X.debug.fd (fun _ => True) (fun _ => H c DB n (.Vptr bl ol) gv) _ _
      (X.sDebug n _ gv L) X.debug.fp X.debug.ty rfl (fun le m _ => ev_callee X.debug rfl)
      (fun le m hT => .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
        (hdataPtr m) (.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl
        (.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (hlineC m _)
        (.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ (.Vlong L) (hT.get (by temps_get))) rfl .nil))))
      (fun h hH => ⟨rfl, hH⟩) (fun v h hs => ⟨trivial, hs⟩) (fun _ _ => ?_)
    -- result = Curl_client_write(data, CLIENTWRITE_INFO, line, length);
    refine Sep.triple_seq ge _ _ _
      (fun e le hp => ∃ r1, LocalSt (envE c.bg c.bb)
        (setLocal (setLocal (setLocal (setLocal l _length (.Vlong L)) _t'9 v9) _t'10 (.Vint r1))
          _result (.Vint r1)) (H c DB n (.Vptr bl ol) gv) e le hp)
      _ _ _ ?_ ?_
    · refine triple_weaken_only ge _ _ ?_
      refine Sep.triple_seq ge _ _ _ _ _ _ _
        (call_some ge _ _ (writeSpec c DB n (.Vptr bl ol) gv L) _t'10 _ _ _ _ _
          [.Vptr c.dataB c.dataO, .Vint (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 1)),
           .Vptr bl ol, .Vlong L] X.write.b X.write.fd (fun v => ∃ r1, v = .Vint r1)
          (fun _ => H c DB n (.Vptr bl ol) gv)
          (X.sWrite n _ gv L) X.write.fp X.write.ty rfl (fun le m _ => ev_callee X.write rfl)
          (fun le m hT => .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
            (hdataPtr m) (.cons _ _ _ _ _ _ _
              (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) (EvalExpr.Econst_int _ _) rfl) rfl
            (.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (hlineC m _)
            (.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ (.Vlong L) (hT.get (by temps_get))) rfl .nil))))
          (fun h hH => ⟨rfl, hH⟩) (fun v h hs => hs))
        (triple_exists ge _ _ _ _ _ (fun v => triple_pure ge _ _ _ _ _ _ (fun hv => ?_)))
      obtain ⟨r1, rfl⟩ := hv
      exact Sep.triple_conseq ge _ _
        (triple_set_local_fwd ge _ _ _ _ _ _result _ (.Vint r1)
          (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _))))
        (fun _ _ _ x => x) (fun _ _ _ h => ⟨r1, h⟩) (fun _ _ _ x => False.elim x)
        (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
    refine triple_exists ge _ _ _ _ _ (fun r1 => ?_)
    have hsub3 : ∀ q ∈ lI c mx r1, q ∈
        setLocal (setLocal (setLocal (setLocal l _length (.Vlong L)) _t'9 v9) _t'10 (.Vint r1))
          _result (.Vint r1) :=
      lI_set_result (sub_setLocal (sub_setLocal (sub_setLocal hsub (by lI_ne)) (by lI_ne)) (by lI_ne))
    -- if(result) return result;
    refine Sep.triple_seq ge _ _ _
      (LocalSt (envE c.bg c.bb)
        (setLocal (setLocal (setLocal (setLocal l _length (.Vlong L)) _t'9 v9) _t'10 (.Vint r1))
          _result (.Vint r1)) (H c DB n (.Vptr bl ol) gv)) _ _ _ ?_ ?_
    · cases hb : !Integers.Int.eq r1 Integers.Int.zero with
      | true =>
        refine triple_if_local ge _ _ _ _ _ _ true _ _ _
          (fun le m _ hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _)),
            by rw [← hb]; rfl⟩) ?_
        exact ret_val ge _ X.cenv c X.bgbb DB n _ gv _ _ (.Vint r1) _ _ _
          (fun _ _ hT => EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _))) (fun _ => rfl)
      | false =>
        refine triple_if_local ge _ _ _ _ _ _ false _ _ _
          (fun le m _ hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _)),
            by rw [← hb]; rfl⟩) ?_
        exact Sep.triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x) (fun _ _ _ x => x)
          (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
    -- if(pp->endofresp(data, conn, line, length, code)) { ... break; }
    refine Sep.triple_seq ge _ _ _
      (fun e le hp => ∃ b, LocalSt (envE c.bg c.bb)
        (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal l _length (.Vlong L)) _t'9 v9)
          _t'10 (.Vint r1)) _result (.Vint r1)) _t'18 (.Vptr c.eorB Integers.Ptrofs.zero))
          _t'13 (Val.ofBool b)) (H c DB n (.Vptr bl ol) gv) e le hp)
      _ _ _ ?_ ?_
    · refine Sep.triple_seq ge _ _ _
        (fun e le hp => ∃ b, LocalSt (envE c.bg c.bb)
          (setLocal (setLocal (setLocal (setLocal (setLocal (setLocal l _length (.Vlong L)) _t'9 v9)
            _t'10 (.Vint r1)) _result (.Vint r1)) _t'18 (.Vptr c.eorB Integers.Ptrofs.zero))
            _t'13 (Val.ofBool b)) (H c DB n (.Vptr bl ol) gv) e le hp)
        _ _ _ ?_ ?_
      · refine triple_weaken_only ge _ _ ?_
        refine triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ _ _ _ _t'18 _ (.Vptr c.eorB Integers.Ptrofs.zero)
            (fun le m hp hT hH hag => eval_field (hT.get (by temps_get))
              (by rw [X.cenv]; exact co_pp) (by rw [X.cenv]; exact off_eor) rfl
              (fixed_load (k := 8) (hk := by simp [cells]) rfl X.pmR hH hag))) ?_
        refine Sep.triple_conseq ge _ _
          (call_some ge _ _ (eorSpec c DB n (.Vptr bl ol) gv L) _t'13 _ _ _ _ _
            [.Vptr c.dataB c.dataO, c.connV, .Vptr bl ol, .Vlong L, .Vptr c.codeB c.codeO]
            c.eorB X.eorFd (fun v => ∃ b, v = Val.ofBool b) (fun _ => H c DB n (.Vptr bl ol) gv)
            (X.sEor n _ gv L) X.eor_fp X.eor_ty rfl
            (fun le m hT => eval_callee_temp (hT.get (mem_setLocal_head _ _ _)))
            (fun le m hT => .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
              (hdataPtr m) (.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
              (cast_ptr X.connPtr _ _ m)
              (.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (hlineC m _)
              (.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ (.Vlong L) (hT.get (by temps_get))) rfl
              (.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) rfl .nil)))))
            (fun h hH => ⟨rfl, hH⟩) (fun v h hs => hs))
          (fun _ _ _ x => x) (fun _ _ _ ⟨v, ⟨b, hv⟩, hL⟩ => ⟨b, by rw [← hv]; exact hL⟩)
          (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
      · refine triple_exists ge _ _ _ _ _ (fun b => ?_)
        exact Sep.triple_conseq ge _ _
          (eor_ok X _ mx r1 n _ gv L b (J2 c DB mx gv n)
            (sub_setLocal (sub_setLocal hsub3 (by lI_ne)) (by lI_ne)) (by temps_get)
            (mem_setLocal_head _ _ _))
          (fun _ _ _ x => x) (fun _ _ _ h => ⟨b, h⟩) (fun _ _ _ x => x) (fun _ _ _ x => x)
          (fun _ _ x => x)
    · refine triple_exists ge _ _ _ _ _ (fun b => ?_)
      exact tail_ok X _ mx r1 n _ gv L _ _
        (sub_setLocal (sub_setLocal hsub3 (by lI_ne)) (by lI_ne)) (by temps_get) hL1 hLn

/-! ## 内側のループの本体とループ全体 -/

set_option maxHeartbeats 4000000 in
theorem inner_body (X : Ext c DB ge) (mx r : Integers.Int) (gv : Val) (n : Nat) (p : Val) :
    Triple ge (FunctionEntry2 ge) f_Curl_pp_readresp
      (LocalSt (envE c.bg c.bb) (lI c mx r) (H c DB n p gv)) innerBody
      (RetOK (J2 c DB mx gv n) (Post2 c DB mx gv) (J2 c DB mx gv n)) := by
  refine with_db X (fun hptr hn => ?_)
  -- line = curlx_dyn_ptr(&pp->recvbuf);
  refine Sep.triple_seq ge _ _ _
    (LocalSt (envE c.bg c.bb) (setLocal (setLocal (lI c mx r) _t'6 p) _line p) (H c DB n p gv))
    _ _ _ ?_ ?_
  · refine call_some_then (ptrSpec c DB n p gv) _t'6 _ _ _ _ _ [rbV c] X.ptr.b X.ptr.fd
      (fun v => v = p) (fun _ => H c DB n p gv) _ _
      (X.sPtr n p gv) X.ptr.fp X.ptr.ty rfl (fun le m _ => ev_callee X.ptr rfl)
      (fun le m hT => args_rb X (hT.get (by temps_get))) (fun h hH => ⟨rfl, hH⟩)
      (fun v h hs => hs) (fun v hv => ?_)
    subst hv
    exact triple_weaken_only ge _ _ (triple_set_local_fwd ge _ _ _ _ _ _line _ v
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _))))
  -- nl = memchr(line, '\n', curlx_dyn_len(&pp->recvbuf));
  refine Sep.triple_seq ge _ _ _
    (fun e le hp => ∃ v8, InRange p (Integers.Int64.repr n) v8 ∧ LocalSt (envE c.bg c.bb)
      (setLocal (setLocal (setLocal (setLocal (setLocal (lI c mx r) _t'6 p) _line p) _t'7
        (.Vlong (Integers.Int64.repr n))) _t'8 v8) _nl v8) (H c DB n p gv) e le hp)
    _ _ _ ?_ ?_
  · refine Sep.triple_seq ge _ _ _
      (fun e le hp => ∃ v8, InRange p (Integers.Int64.repr n) v8 ∧ LocalSt (envE c.bg c.bb)
        (setLocal (setLocal (setLocal (setLocal (lI c mx r) _t'6 p) _line p) _t'7
          (.Vlong (Integers.Int64.repr n))) _t'8 v8) (H c DB n p gv) e le hp)
      _ _ _ ?_ ?_
    · refine call_some_then (lenSpec c DB n p gv) _t'7 _ _ _ _ _ [rbV c] X.len.b X.len.fd
        (fun v => v = .Vlong (Integers.Int64.repr n)) (fun _ => H c DB n p gv) _ _
        (X.sLen n p gv) X.len.fp X.len.ty rfl (fun le m _ => ev_callee X.len rfl)
        (fun le m hT => args_rb X (hT.get (by temps_get))) (fun h hH => ⟨rfl, hH⟩)
        (fun v h hs => hs) (fun v hv => ?_)
      subst hv
      exact triple_weaken_only ge _ _
        (call_some ge _ _ (memchrSpec c DB n p gv (Integers.Int64.repr n) (Integers.Int.repr 10))
          _t'8 _ _ _ _ _ [p, .Vint (Integers.Int.repr 10), .Vlong (Integers.Int64.repr n)]
          X.memchr.b X.memchr.fd (InRange p (Integers.Int64.repr n)) (fun _ => H c DB n p gv)
          (X.sMemchr n p gv _ _) X.memchr.fp X.memchr.ty rfl (fun le m _ => ev_callee X.memchr rfl)
          (fun le m hT => .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
            (cast_ptr hptr _ _ m) (.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl
            (.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _))) rfl
              .nil)))
          (fun h hH => ⟨rfl, by rw [uns_repr n hn]; exact Int.le_refl _, hH⟩) (fun v h hs => hs))
    · refine triple_exists ge _ _ _ _ _ (fun v8 => triple_pure ge _ _ _ _ _ _ (fun hin => ?_))
      exact Sep.triple_conseq ge _ _
        (triple_set_local_fwd ge _ _ _ _ _ _nl _ v8
          (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (mem_setLocal_head _ _ _))))
        (fun _ _ _ x => x) (fun _ _ _ h => ⟨v8, hin, h⟩) (fun _ _ _ x => False.elim x)
        (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)
  · refine triple_exists ge _ _ _ _ _ (fun v8 => triple_pure ge _ _ _ _ _ _ (fun hin => ?_))
    exact nl_ok X _ mx r n p gv v8
      (sub_setLocal (sub_setLocal (sub_setLocal (sub_setLocal (sub_setLocal (fun _ x => x)
        (by lI_ne)) (by lI_ne)) (by lI_ne)) (by lI_ne)) (by lI_ne))
      (by temps_get) (mem_setLocal_head _ _ _) hin

/-- **内側のループは止まる**（受信バッファの長さ `n` が減少量）。 -/
theorem inner_loop (X : Ext c DB ge) (mx : Integers.Int) (gv : Val) (B C : Sep.Assn) :
    ∀ n, Triple ge (FunctionEntry2 ge) f_Curl_pp_readresp (I2 c DB mx gv n)
      (.Sloop innerBody .Sskip) (RetOK (Post2 c DB mx gv) B C) :=
  Sep.triple_loop ge _ _ (RetOK (Post2 c DB mx gv) B C) (I2 c DB mx gv) (J2 c DB mx gv)
    innerBody .Sskip
    (fun n => triple_exists ge _ _ _ _ _ (fun p => triple_exists ge _ _ _ _ _
      (fun r => inner_body X mx r gv n p)))
    (fun n => Sep.triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x))

end Case1C
