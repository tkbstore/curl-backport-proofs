/-
Case 1: 文の規則を、この関数のメモリの形（`H`）に合わせたもの。

- セルの読み出し・書き込み（`cells` の k 番目を取り出して戻す）
- 呼び出し（呼ばれる側にはメモリ全体 `H` を渡し、同じ形で返してもらう）
- `return`（局所変数 gotbytes・buffer の解放を含む）
-/
import Case1Common
open CC CC.Sep CC.HProp
open Case1_after
open Case5C (addr)
open Case4C (IsPtr)

set_option maxRecDepth 20000

namespace Case1C

/-! ## 存在と純粋な条件の取り出し -/

theorem seq_ex {α : Sort u} (ge fe f) (P : Sep.Assn) (X : α → Sep.Assn) (R : Sep.ExitConds)
    (s1 s2 : Stmt)
    (h1 : Triple ge fe f P s1 (.only (fun e le hp => ∃ x, X x e le hp)))
    (h2 : ∀ x, Triple ge fe f (X x) s2 R) :
    Triple ge fe f P (.Ssequence s1 s2) R :=
  triple_seq_fwd ge fe f P _ R s1 s2 h1 (triple_exists ge fe f X s2 R h2)

theorem triple_pure (ge fe f) (φ : Prop) (P : Sep.Assn) (s : Stmt) (R : Sep.ExitConds)
    (h : φ → Triple ge fe f P s R) :
    Triple ge fe f (fun e le hp => φ ∧ P e le hp) s R := by
  intro k e le hp hf m hd hag hP
  exact h hP.1 k e le hp hf m hd hag hP.2

/-! ## セル -/

theorem cell_split {c : Ctx} {DB : Nat → Val → HProp} {n : Nat} {p gv : Val} {k : Nat}
    {hk : k < (cells c).length} {ch : Chunk} {pm : Permission} {b : Block} {o : Z}
    {C : Val → Prop} (hcell : (cells c)[k]'hk = cellP ch pm b o C) {hp : Heap}
    (hH : H c DB n p gv hp) :
    ∃ v h1 h2, Heap.disjoint h1 h2 ∧ hp = Heap.union h1 h2 ∧ C v ∧ mapsto ch pm b o v h1
      ∧ Rk c DB n p gv k h2 := by
  rw [H_pick c DB n p gv k hk, hcell] at hH
  obtain ⟨h1, h2, hd, heq, ⟨v, hv⟩, hR⟩ := hH
  obtain ⟨hC, hm⟩ := pure_sep_elim hv
  exact ⟨v, h1, h2, hd, heq, hC, hm, hR⟩

theorem cell_join {c : Ctx} {DB : Nat → Val → HProp} {n : Nat} {p gv : Val} {k : Nat}
    {hk : k < (cells c).length} {ch : Chunk} {pm : Permission} {b : Block} {o : Z}
    {C : Val → Prop} (hcell : (cells c)[k]'hk = cellP ch pm b o C) {v : Val} {h1 h2 : Heap}
    (hd : Heap.disjoint h1 h2) (hC : C v) (hm : mapsto ch pm b o v h1)
    (hR : Rk c DB n p gv k h2) :
    H c DB n p gv (Heap.union h1 h2) := by
  rw [H_pick c DB n p gv k hk, hcell]
  exact ⟨h1, h2, hd, rfl, ⟨v, pure_sep_intro hC hm⟩, hR⟩

/-- `k` 番目のセルの読み出し。 -/
theorem cell_load {c : Ctx} {DB : Nat → Val → HProp} {n : Nat} {p gv : Val} {k : Nat}
    {hk : k < (cells c).length} {ch : Chunk} {pm : Permission} {b : Block} {o : Z}
    {C : Val → Prop} (hcell : (cells c)[k]'hk = cellP ch pm b o C)
    (hpr : permOrder pm .Readable = true) {hp : Heap} {m : Mem}
    (hH : H c DB n p gv hp) (hag : Heap.Agrees hp m) :
    ∃ v, C v ∧ Mem.load ch m b o = some (Val.loadResult ch v) := by
  obtain ⟨v, h1, h2, _, rfl, hC, hm, _⟩ := cell_split hcell hH
  exact ⟨v, hC, mapsto_load hpr hm (Heap.Agrees_union_left hag)⟩

/-- 値の決まったセル（`data->conn`・`pp->endofresp`）の読み出し。 -/
theorem fixed_load {c : Ctx} {DB : Nat → Val → HProp} {n : Nat} {p gv : Val} {k : Nat}
    {hk : k < (cells c).length} {ch : Chunk} {pm : Permission} {b : Block} {o : Z}
    {v : Val} (hcell : (cells c)[k]'hk = mapsto ch pm b o v)
    (hpr : permOrder pm .Readable = true) {hp : Heap} {m : Mem}
    (hH : H c DB n p gv hp) (hag : Heap.Agrees hp m) :
    Mem.load ch m b o = some (Val.loadResult ch v) := by
  rw [H_pick c DB n p gv k hk, hcell] at hH
  obtain ⟨h1, h2, _, rfl, hm, _⟩ := hH
  exact mapsto_load hpr hm (Heap.Agrees_union_left hag)

theorem got_load {c : Ctx} {DB : Nat → Val → HProp} {n : Nat} {p gv : Val} {hp : Heap} {m : Mem}
    (hH : H c DB n p gv hp) (hag : Heap.Agrees hp m) :
    Mem.load .Mint64 m c.bg 0 = some (Val.loadResult .Mint64 gv) := by
  obtain ⟨h1, h2, _, rfl, hm, _⟩ := hH
  exact mapsto_load rfl hm (Heap.Agrees_union_left hag)

/-- `k` 番目のセルへの書き込み。書く値が `C` を満たせば、メモリの形は変わらない。 -/
theorem assign_cell (ge fe f) (c : Ctx) (DB : Nat → Val → HProp) (n : Nat) (p gv : Val)
    (E : Env) (l : List (Ident × Val)) (k : Nat) (hk : k < (cells c).length)
    (ch : Chunk) (pm : Permission) (b : Block) (o : Integers.Ptrofs) (C : Val → Prop)
    (hcell : (cells c)[k]'hk = cellP ch pm b (Integers.Ptrofs.unsigned o) C)
    (a1 a2 : Expr) (hpw : permOrder pm .Writable = true)
    (hacc : accessMode (typeof a1) = .By_value ch)
    (hlv : ∀ le m, TempsHold l le → EvalLvalue ge E le m a1 b o .Full)
    (hrhs : ∀ le m hp, TempsHold l le → H c DB n p gv hp → Heap.Agrees hp m →
      ∃ v2 vnew, EvalExpr ge E le m a2 v2
        ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some vnew ∧ C vnew) :
    Triple ge fe f (LocalSt E l (H c DB n p gv)) (.Sassign a1 a2)
      (.only (LocalSt E l (H c DB n p gv))) := by
  refine triple_assign ge fe f _ _ a1 a2 ch pm b o hpw hacc (fun e le hp m hP hag => ?_)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  obtain ⟨v2, vnew, hev, hcast, hC⟩ := hrhs le m hp hT hH hag
  obtain ⟨vold, h1, h2, hd, rfl, _, hm, hR⟩ := cell_split hcell hH
  exact ⟨vold, vnew, h1, h2, hd, rfl, hm, hlv le m hT, ⟨v2, hev, hcast⟩,
    fun h1' hm' hd' => ⟨rfl, hT, cell_join hcell hd' hC hm' hR⟩⟩

/-- `gotbytes = a2;` -/
theorem assign_got (ge fe f) (c : Ctx) (DB : Nat → Val → HProp) (n : Nat) (p gv : Val)
    (E : Env) (l : List (Ident × Val)) (hE : E.get _gotbytes = some (c.bg, tulong))
    (a2 : Expr) (vnew : Val)
    (hrhs : ∀ le m, TempsHold l le →
      ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) tulong m = some vnew) :
    Triple ge fe f (LocalSt E l (H c DB n p gv)) (.Sassign (.Evar _gotbytes tulong) a2)
      (.only (LocalSt E l (H c DB n p vnew))) := by
  refine triple_assign ge fe f _ _ _ a2 .Mint64 .Freeable c.bg Integers.Ptrofs.zero rfl rfl
    (fun e le hp m hP hag => ?_)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  obtain ⟨v2, hev, hcast⟩ := hrhs le m hT
  obtain ⟨h1, h2, hd, rfl, hm, hR⟩ := hH
  refine ⟨gv, vnew, h1, h2, hd, rfl, by rw [ptrofs_unsigned_zero]; exact hm,
    EvalLvalue.Evar_local _ _ _ hE, ⟨v2, hev, hcast⟩, fun h1' hm' hd' => ?_⟩
  rw [ptrofs_unsigned_zero] at hm'
  exact ⟨rfl, hT, h1', h2, hd', rfl, hm', hR⟩

/-! ## 呼び出し

呼ばれる側の仕様は、メモリ全体（`Hh`）を受け取って返す形にする。呼ばれる側が所有を分けて返す必要がないので、
呼び出しのたびに所有を組み替えなくてよい。 -/

theorem call_some (ge fe f) (S : FunSpec) (id : Ident) (a : Expr) (al : List Expr)
    (E : Env) (l : List (Ident × Val)) (Hh : HProp) (vargs : List Val) (fb : Block) (fd : FunDef)
    (φ : Val → Prop) (Q : Val → HProp)
    (hspec : ∀ vs, SatisfiesAt ge fe fd S vs) (hfind : FuncPtr ge fb fd)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun (typeof a) = .f S.tyargs S.tyres S.cc)
    (hcallee : ∀ le m, TempsHold l le → EvalExpr ge E le m a (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge E le m al S.tyargs vargs)
    (hpre : ∀ h, Hh h → S.pre vargs h)
    (hpost : ∀ v h, S.post v h → φ v ∧ Q v h) :
    Triple ge fe f (LocalSt E l Hh) (.Scall (some id) a al)
      (.only (fun e le hp => ∃ v, φ v ∧ LocalSt E (setLocal l id v) (Q v) e le hp)) := by
  refine triple_call ge fe f S (some id) a al _ _ fb fd hspec hfind hty hclass
    (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  refine ⟨vargs, hp, Heap.emp, Heap.disjoint_emp_right hp, (Heap.union_emp hp).symm,
    hcallee le m hT, hargs le m hT, hpre hp hH, fun v h1' hS _ => ?_⟩
  obtain ⟨hφ, hQ⟩ := hpost v h1' hS
  refine ⟨v, hφ, rfl, ?_, by rw [Heap.union_emp]; exact hQ⟩
  exact TempsHold_set (fun _ hq => (mem_dropId hq).2) (TempsHold_mono (fun _ hq => (mem_dropId hq).1) hT)

theorem call_none (ge fe f) (S : FunSpec) (a : Expr) (al : List Expr)
    (E : Env) (l : List (Ident × Val)) (Hh : HProp) (vargs : List Val) (fb : Block) (fd : FunDef)
    (φ : Val → Prop) (Q : Val → HProp)
    (hspec : ∀ vs, SatisfiesAt ge fe fd S vs) (hfind : FuncPtr ge fb fd)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun (typeof a) = .f S.tyargs S.tyres S.cc)
    (hcallee : ∀ le m, TempsHold l le → EvalExpr ge E le m a (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge E le m al S.tyargs vargs)
    (hpre : ∀ h, Hh h → S.pre vargs h)
    (hpost : ∀ v h, S.post v h → φ v ∧ Q v h) :
    Triple ge fe f (LocalSt E l Hh) (.Scall none a al)
      (.only (fun e le hp => ∃ v, φ v ∧ LocalSt E l (Q v) e le hp)) := by
  refine triple_call ge fe f S none a al _ _ fb fd hspec hfind hty hclass
    (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  refine ⟨vargs, hp, Heap.emp, Heap.disjoint_emp_right hp, (Heap.union_emp hp).symm,
    hcallee le m hT, hargs le m hT, hpre hp hH, fun v h1' hS _ => ?_⟩
  obtain ⟨hφ, hQ⟩ := hpost v h1' hS
  exact ⟨v, hφ, rfl, hT, by rw [Heap.union_emp]; exact hQ⟩

/-! ## `return`

どの `return` も、局所変数 gotbytes（8 バイト）と buffer（900 バイト）を解放する。所有は `H` の先頭の2つ。
戻ったあとのメモリについては何も求めない（`ret := True`）。この証明で示すのは、戻ることだけである。 -/

/-- 戻ることだけを求める出口の条件。`normal`・`brk`・`cont` は場所ごとに入れ替える。 -/
abbrev RetOK (Q B C : Sep.Assn) : Sep.ExitConds :=
  { normal := Q, brk := B, cont := C, ret := fun _ _ => True }

/-- `h1` の所有は、すべて `h2` にもある。 -/
def Sub (h1 h2 : Heap) : Prop := ∀ b o c, h1 b o = some c → h2 b o = some c

theorem sub_refl (h : Heap) : Sub h h := fun _ _ _ x => x

theorem sub_left (h1 h2 : Heap) : Sub h1 (Heap.union h1 h2) := by
  intro b o c hc
  simp only [Heap.union, hc]

theorem sub_right {h1 h2 : Heap} (hd : Heap.disjoint h1 h2) : Sub h2 (Heap.union h1 h2) := by
  intro b o c hc
  rcases hd b o with h | h
  · simp only [Heap.union, h]; exact hc
  · rw [h] at hc; cases hc

theorem sub_trans {a b c : Heap} (h1 : Sub a b) (h2 : Sub b c) : Sub a c :=
  fun x o v hv => h2 x o v (h1 x o v hv)

theorem sub_union {a b c : Heap} (h1 : Sub a c) (h2 : Sub b c) : Sub (Heap.union a b) c := by
  intro x o v hv
  unfold Heap.union at hv
  cases ha : a x o with
  | some va => rw [ha] at hv; cases hv; exact h1 x o _ ha
  | none => rw [ha] at hv; exact h2 x o v hv

theorem sub_union_mono {a b hf : Heap} (hs : Sub a b) (hd : Heap.disjoint b hf) :
    Sub (Heap.union a hf) (Heap.union b hf) := by
  intro x o v hv
  unfold Heap.union at hv
  cases ha : a x o with
  | some va => rw [ha] at hv; cases hv; simp only [Heap.union, hs x o _ ha]
  | none =>
      rw [ha] at hv
      rcases hd x o with hb | hb
      · simp only [Heap.union, hb]; exact hv
      · rw [hb] at hv; cases hv

theorem agrees_sub {a b : Heap} {m : Mem} (hs : Sub a b) (hag : Heap.Agrees b m) :
    Heap.Agrees a m := fun x o v hv => hag x o v (hs x o v hv)

theorem disjoint_sub {a b hf : Heap} (hs : Sub a b) (hd : Heap.disjoint b hf) :
    Heap.disjoint a hf := by
  intro x o
  rcases hd x o with h | h
  · left
    cases ha : a x o with
    | none => rfl
    | some v => rw [hs x o v ha] at h; cases h
  · exact Or.inr h

theorem none_of_disjoint {a b : Heap} {x : Block} {o : Z} {c : Cell} (hd : Heap.disjoint a b)
    (ha : a x o = some c) : b x o = none :=
  (hd x o).resolve_left (by rw [ha]; simp)

/-- 範囲 `[0, len)` を所有していれば、その範囲の各番地を所有している。 -/
theorem owns_at {h : Heap} {b : Block} {p : Permission} {vl : List MemVal}
    (hb : bytesPtsTo b p 0 vl h) (o : _root_.Int) (h0 : 0 ≤ o) (hlt : o < (vl.length : _root_.Int)) :
    ∃ c, h b o = some c := by
  have hown := bytesPtsTo_ownsRange b p vl 0 h hb
  have hi : o.toNat < vl.length := by omega
  have := hown o.toNat hi
  rw [show (0 : _root_.Int) + ((o.toNat : Nat) : _root_.Int) = o from by omega] at this
  exact ⟨_, this⟩

theorem blocks_envE (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (bg bb : Block) :
    blocksOfEnv ge.genv_cenv (envE bg bb) = [(bb, 0, 900), (bg, 0, 8)] := by
  rw [hcenv]
  rfl

theorem ret_val (ge : CGenv) (fe) (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (c : Ctx) (hbgbb : c.bg ≠ c.bb) (DB : Nat → Val → HProp) (n : Nat) (p gv : Val)
    (l : List (Ident × Val)) (a : Expr) (v : Val) (Q B C : Sep.Assn)
    (hev : ∀ le m, TempsHold l le → EvalExpr ge (envE c.bg c.bb) le m a v)
    (hcast : ∀ m, Cop.semCast v (typeof a) tint m = some v) :
    Triple ge fe f_Curl_pp_readresp (LocalSt (envE c.bg c.bb) l (H c DB n p gv))
      (.Sreturn (some a)) (RetOK Q B C) := by
  refine Sep.triple_conseq ge fe _ (R := RetOK Sep.Assn.no Sep.Assn.no Sep.Assn.no)
    (Sep.triple_return ge fe _ _ _ a (fun e le hp m hP hag => ?_))
    (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x)
    (fun _ _ _ x => False.elim x) (fun _ _ x => x)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  obtain ⟨hg, hrest, hdg, rfl, hmg, hR⟩ := hH
  obtain ⟨hhr, hdb, hd2, rfl, hHr, _⟩ := hR
  obtain ⟨hbuf, hcr, hd3, rfl, hbufP, _⟩ := hHr
  obtain ⟨bytes, hbytes⟩ := hbufP
  obtain ⟨hlen, hbb⟩ := pure_sep_elim hbytes
  obtain ⟨_, hgb⟩ := pure_sep_elim hmg
  have hglen : (encodeVal .Mint64 gv).length = 8 := length_encodeVal _ _
  -- 所有の包含
  have sBuf : Sub hbuf (Heap.union hg (Heap.union (Heap.union hbuf hcr) hdb)) :=
    sub_trans (sub_left _ _) (sub_trans (sub_left _ _) (sub_right hdg))
  have sG : Sub hg (Heap.union hg (Heap.union (Heap.union hbuf hcr) hdb)) := sub_left _ _
  have sCr : Sub hcr (Heap.union (Heap.union hbuf hcr) hdb) :=
    sub_trans (sub_right hd3) (sub_left _ _)
  have sDb : Sub hdb (Heap.union (Heap.union hbuf hcr) hdb) := sub_right hd2
  have sRest : Sub (Heap.union hcr hdb)
      (Heap.union hg (Heap.union (Heap.union hbuf hcr) hdb)) :=
    sub_trans (sub_union sCr sDb) (sub_right hdg)
  -- 解放できること
  have hrpB : Mem.rangePerm m c.bb 0 900 .Cur .Freeable = true := by
    have := bytesPtsTo_rangePerm hbb (agrees_sub sBuf hag)
    rwa [hlen] at this
  have hrpG : Mem.rangePerm m c.bg 0 8 .Cur .Freeable = true := by
    have := bytesPtsTo_rangePerm hgb (agrees_sub sG hag)
    rwa [hglen] at this
  obtain ⟨m', hm'⟩ := freeList_isSome_of_rangePerm [(c.bb, 0, 900), (c.bg, 0, 8)] m
    (fun blk hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl
      · exact hrpB
      · exact hrpG)
    (by simp; exact fun h => hbgbb h.symm)
  refine ⟨v, v, m', Heap.union hcr hdb, hev le m hT, hcast m,
    by rw [blocks_envE ge hcenv]; exact hm', trivial, fun hf hd hagf => ?_⟩
  refine ⟨disjoint_sub sRest hd, ?_⟩
  refine Sep.Agrees_freeList [(c.bb, 0, 900), (c.bg, 0, 8)] m m' hm' ?_
    (agrees_sub (sub_union_mono sRest hd) hagf)
  intro blk hb ofs h0 hlt
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
  have hcd : ∀ (X : Heap) (cX : Cell), X blk.1 ofs = some cX →
      Sub X (Heap.union hg (Heap.union (Heap.union hbuf hcr) hdb)) →
      Heap.disjoint X hcr → Heap.disjoint X hdb →
      Heap.union (Heap.union hcr hdb) hf blk.1 ofs = none := by
    intro X cX hX sX dCr dDb
    have e1 := none_of_disjoint dCr hX
    have e2 := none_of_disjoint dDb hX
    have e3 : hf blk.1 ofs = none :=
      none_of_disjoint (disjoint_sub sX hd) hX
    simp only [Heap.union, e1, e2, e3]
  rcases hb with rfl | rfl
  · obtain ⟨cB, hcB⟩ := owns_at hbb ofs h0 (by rw [hlen]; exact hlt)
    exact hcd hbuf cB hcB sBuf hd3 (disjoint_sub (sub_left _ _) hd2)
  · obtain ⟨cG, hcG⟩ := owns_at hgb ofs h0 (by rw [hglen]; exact hlt)
    exact hcd hg cG hcG sG (Heap.disjoint_comm (disjoint_sub sCr (Heap.disjoint_comm hdg)))
      (Heap.disjoint_comm (disjoint_sub sDb (Heap.disjoint_comm hdg)))


end Case1C
