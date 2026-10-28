/-
CVE-2026-3805: 上流の修正後（e090be9f73）の `smb_parse_url_path`（U1）。

証明すること（`parse_after`）: 戻り値が CURLE_OK なら、`smbc->share` はブロック `bs` の先頭、`req->path` はブロック `bq` の先頭を指し、
2つの文字列は分離した所有（`∗`）として事後条件にある（`P1_C` で `bs ≠ bq` を取り出す）。
-/
import Deb2026_3805Seg
open CC CC.Sep CC.HProp
open Deb2026_3805_up_after
open Case5C (addr RR boolVal_ofBool_tint)
open Case4debC (IsPtr loadResult_ptr cast_ptr)

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Deb2026_3805C

macro "lmem" : tactic => `(tactic| (
  try dsimp only [Lk, Lb]
  repeat (first | exact List.mem_cons_self .. | apply List.mem_cons_of_mem)))

macro "lsub" : tactic => `(tactic| (
  try dsimp only [Lk, Lb]
  repeat' (first | exact fun _ h => absurd h List.not_mem_nil | refine List.forall_mem_cons.mpr ⟨?_, ?_⟩)
  all_goals lmem))

macro "lfresh" : tactic => `(tactic| (
  try dsimp only [Lk, Lb]
  repeat' (first | exact fun _ h => absurd h List.not_mem_nil | refine List.forall_mem_cons.mpr ⟨?_, ?_⟩)
  all_goals (try dsimp only)
  all_goals decide))

macro "eval_one2" : tactic => `(tactic| (first
    | rfl
    | exact EvalExpr.Econst_int _ _
    | exact EvalExpr.Etempvar _ _ _ ((‹TempsHold _ _›).get (by lmem))
    | exact EvalExpr.Eaddrof _ _ _ _ (eval_var_local (envP_path _))
    | exact cast_ptr ‹IsPtr _› _ _ _
    | (refine EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) ?_; rfl)))

macro "eval_args2" : tactic => `(tactic| (
  repeat' (first | exact EvalExprlist.nil | refine EvalExprlist.cons _ _ _ _ ?_ _ _ ?_ ?_ ?_)
  all_goals try eval_one2
  all_goals try eval_one2))

macro "lfresh3" : tactic => `(tactic| (
  try dsimp only [Lk, Lb]
  repeat' (first | exact fun _ h => absurd h List.not_mem_nil | refine List.forall_mem_cons.mpr ⟨?_, ?_⟩)
  all_goals (try dsimp only)
  all_goals (refine ⟨?_, ?_, ?_⟩ <;> decide)))

/-- 呼び出し（戻り値を一時変数に入れる。並びは先頭に足すだけ）。 -/
theorem call2 (ge fe f) (S : FunSpec) (id : Ident) (a : Expr) (al : List Expr)
    (E : Env) (l : List (Ident × Val)) (Hpre Hkeep : HProp) (vargs : List Val)
    (fb : Block) (fd : FunDef)
    (hspec : ∀ vs, SatisfiesAt ge fe fd S vs) (hfind : FuncPtr ge fb fd)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun (typeof a) = .f S.tyargs S.tyres S.cc)
    (hne : ∀ q ∈ l, q.1 ≠ id)
    (hcallee : ∀ le m, TempsHold l le → EvalExpr ge E le m a (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge E le m al S.tyargs vargs)
    (hpre : ∀ h, Hpre h → S.pre vargs h) :
    Triple ge fe f (LocalSt E l (Hpre ∗ Hkeep)) (.Scall (some id) a al)
      (.only (fun e le hp => ∃ v, LocalSt E ((id, v) :: l) (S.post v ∗ Hkeep) e le hp)) := by
  refine triple_conseq ge fe f
    (triple_call_local_ex ge fe f S id a al E l l Hpre Hkeep vargs fb fd hspec hfind hty hclass
      (fun _ h => h) hne hcallee hargs hpre)
    (fun _ _ _ x => x) (fun e le hp ⟨v, he, hT, hH⟩ => ⟨v, he, hT, hH⟩)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

/-- 一時変数への代入（並びは先頭に足すだけ）。 -/
theorem set2 (ge fe f) (E : Env) (l : List (Ident × Val)) (H : HProp) (id : Ident) (a : Expr) (v : Val)
    (hne : ∀ q ∈ l, q.1 ≠ id)
    (hev : ∀ le m hp, TempsHold l le → H hp → Heap.Agrees hp m → EvalExpr ge E le m a v) :
    Triple ge fe f (LocalSt E l H) (.Sset id a) (.only (LocalSt E ((id, v) :: l) H)) :=
  triple_set_local ge fe f E l l H id a v (fun _ h => h) hne hev

abbrev E (bp : Block) : Env := envP bp
abbrev Lk (c : Ctx) : List (Ident × Val) := Lb c

/-- urldecode のあとに残る所有。 -/
abbrev K1 (c : Ctx) : HProp := cD c ∗ cS c c.oldV ∗ ownStr c.oldV ∗ cR c c.reqV ∗ emp

def Q1 (c : Ctx) (bp : Block) : Sep.Assn := fun e le hp =>
  ∃ v, LocalSt (E bp) ((_result, v) :: Lk c) ((udSpec bp).post v ∗ K1 c) e le hp

theorem s1 (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx)
    (hup : IsPtr c.upV) (X : Ext ge) (bp : Block) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path
      (LocalSt (E bp) (Lk c) (H0 c ∗ Case3C.Locs [(bp, 8)])) hd0 (RR (ppPostA c) (Q1 c bp)) := by
  obtain ⟨bU, fdU, hsU, hfU, htU, hU⟩ := X.ud
  refine only_RR _ _ _ _ ?_
  have hcell : H0 c ∗ Case3C.Locs [(bp, 8)]
      = mapsto Mptr .Freeable c.dataB (Integers.Ptrofs.unsigned c.dataO) c.upV
        ∗ (cS c c.oldV ∗ ownStr c.oldV ∗ cR c c.reqV ∗ Case3C.Locs [(bp, 8)]) := by
    unfold H0 cD; ac_rfl
  have hre : H0 c ∗ Case3C.Locs [(bp, 8)] = anyBytes .Freeable bp 0 8 ∗ K1 c := by
    simp only [H0, Case3C.Locs, K1]; ac_rfl
  refine triple_seq_fwd ge _ _ _
    (fun e le hp => ∃ v, LocalSt (E bp) ((_t'1, v) :: (_t'24, c.upV) :: Lk c)
      ((udSpec bp).post v ∗ K1 c) e le hp) _ _ _
    (triple_seq_fwd ge _ _ _ (LocalSt (E bp) ((_t'24, c.upV) :: Lk c) (H0 c ∗ Case3C.Locs [(bp, 8)]))
      _ _ _ ?a ?b) ?c
  case a =>
    refine set2 ge _ _ (E bp) _ _ _t'24 _ c.upV (by lfresh) ?_
    intro le m hp hT hH hag
    exact eval_load (lv_upPath (b := c.dataB) (o := c.dataO) hcenv (hT.get (by lmem))) rfl
      (cell_load hcell hH hag hup)
  case b =>
    rw [hre]
    refine call2 ge _ _ (udSpec bp) _t'1 _ _ (E bp) _ (anyBytes .Freeable bp 0 8) (K1 c)
      [c.upV, .Vlong (Integers.Int64.repr 0), .Vptr bp Integers.Ptrofs.zero,
       .Vlong (Integers.Int64.repr 0), .Vint (Integers.Int.repr 3)] bU fdU
      (hU bp) hfU htU ?hcl (by lfresh) ?cal ?args (fun h hh => hh)
    case hcl => rfl
    case cal => exact fun _ _ _ => eval_callee_global (envP_other _ _ (by decide)) hsU rfl
    case args =>
      intro le m hT
      dsimp only [udSpec]
      eval_args2
  case c =>
    refine triple_conseq ge _ _ (ex_map ge _ _
      (fun v => LocalSt (E bp) ((_t'1, v) :: (_t'24, c.upV) :: Lk c) ((udSpec bp).post v ∗ K1 c))
      (fun v => LocalSt (E bp) ((_result, v) :: (_t'1, v) :: (_t'24, c.upV) :: Lk c)
        ((udSpec bp).post v ∗ K1 c)) _ ?h) (fun _ _ _ x => x) ?n
      (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
    case h =>
      intro v
      refine set2 ge _ _ (E bp) _ _ _result _ v (by lfresh) ?_
      intro le m hp hT _ _
      exact EvalExpr.Etempvar _ _ _ (hT.get (by lmem))
    case n =>
      intro e le hp ⟨v, he, hT, hH⟩
      exact ⟨v, he, TempsHold_mono (by lsub) hT, hH⟩

theorem int_eq_false {r : Integers.Int} (hr : r ≠ Integers.Int.zero) :
    Integers.Int.eq r Integers.Int.zero = false := by
  cases h : Integers.Int.eq r Integers.Int.zero
  · rfl
  · exact absurd (by simpa [Integers.Int.eq, Integers.MI.eq] using h) hr

abbrev PS : Type := Block × (Nat → Integers.Int) × Nat

def Q2 (c : Ctx) (bp : Block) : Sep.Assn := fun e le hp =>
  ∃ x : PS, LocalSt (E bp) (Lk c)
    ((cP bp (.Vptr x.1 Integers.Ptrofs.zero) ∗ strAt x.1 x.2.1 x.2.2) ∗ K1 c) e le hp

theorem s2 (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx) (bp : Block) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (Q1 c bp) hd1 (RR (ppPostA c) (Q2 c bp)) := by
  refine triple_lift ge _ _
    (fun v => LocalSt (E bp) ((_result, v) :: Lk c) ((udSpec bp).post v ∗ K1 c)) _ _ _
    (fun e le hp h => h) ?_
  intro v
  refine lift_or ge _ _ (E bp) _
    (fun hp => ∃ x : PS, v = .Vint Integers.Int.zero
      ∧ (mapsto Mptr .Freeable bp 0 (.Vptr x.1 Integers.Ptrofs.zero) ∗ strAt x.1 x.2.1 x.2.2) hp)
    (fun hp => ∃ r : Integers.Int, (v = .Vint r ∧ r ≠ Integers.Int.zero) ∧ anyBytes .Freeable bp 0 8 hp)
    (K1 c) _ _ ?ok ?err
  case ok =>
    refine lift_heap ge _ _ (E bp) _ (fun x : PS => mapsto Mptr .Freeable bp 0 (.Vptr x.1 Integers.Ptrofs.zero)
      ∗ strAt x.1 x.2.1 x.2.2) (fun _ => v = .Vint Integers.Int.zero) (K1 c) _ _ ?_
    intro x hv
    subst hv
    refine triple_if_local ge _ _ (E bp) _ _ _ false _ _ _ ?_ ?_
    · intro le m hp hT _ _
      exact ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by lmem)), rfl⟩
    · exact triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x)
        (fun e le hp ⟨he, hT, hH⟩ => ⟨x, he, TempsHold_mono (by lsub) hT, hH⟩)
        (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
  case err =>
    refine lift_heap ge _ _ (E bp) _ (fun _ : Integers.Int => anyBytes .Freeable bp 0 8)
      (fun r => v = .Vint r ∧ r ≠ Integers.Int.zero) (K1 c) _ _ ?_
    intro r ⟨hv, hr⟩
    subst hv
    refine triple_if_local ge _ _ (E bp) _ _ _ true _ _ _ ?_ ?_
    · intro le m hp hT _ _
      refine ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by lmem)), ?_⟩
      show some (!Integers.Int.eq r Integers.Int.zero) = some true
      rw [int_eq_false hr]; rfl
    · have he : anyBytes .Freeable bp 0 8 ∗ K1 c
          = (cD c ∗ cS c c.oldV ∗ ownStr c.oldV ∗ cR c c.reqV) ∗ Case3C.Locs [(bp, 8)] := by
        simp only [K1, Case3C.Locs]; ac_rfl
      rw [he]
      refine ret_here ge _ _ hcenv bp _ _ _ (.Vint r) (.Vint r) _ _ ?_ (fun _ => rfl)
        (fun hp _ => post_err c r hr hp)
      intro le m hp hT _ _
      exact EvalExpr.Etempvar _ _ _ (hT.get (by lmem))

/-- `Curl_safefree(smbc->share)` のあとに残る所有。 -/
abbrev H3 (c : Ctx) (bp : Block) (x : PS) : HProp :=
  cS c nullV ∗ cP bp (.Vptr x.1 Integers.Ptrofs.zero) ∗ strAt x.1 x.2.1 x.2.2 ∗ cD c ∗ cR c c.reqV ∗ emp

def Q3 (c : Ctx) (bp : Block) : Sep.Assn := fun e le hp =>
  ∃ x : PS, LocalSt (E bp) (Lk c) (H3 c bp x) e le hp

theorem s3 (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx) (hold : IsPtr c.oldV)
    (X : Ext ge) (bp : Block) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (Q2 c bp) hd2 (RR (ppPostA c) (Q3 c bp)) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.free
  refine only_RR _ _ _ _ (ex_map ge _ _ _ _ _ ?_)
  intro x
  refine once_loop ge _ _ _ _ _ ?_
  have h1 : (cP bp (.Vptr x.1 Integers.Ptrofs.zero) ∗ strAt x.1 x.2.1 x.2.2) ∗ K1 c
      = mapsto Mptr .Freeable c.smbcB (Integers.Ptrofs.unsigned c.smbcO) c.oldV
        ∗ (ownStr c.oldV ∗ cP bp (.Vptr x.1 Integers.Ptrofs.zero) ∗ strAt x.1 x.2.1 x.2.2 ∗ cD c
           ∗ cR c c.reqV ∗ emp) := by
    simp only [K1, cS]; ac_rfl
  have h2 : (cP bp (.Vptr x.1 Integers.Ptrofs.zero) ∗ strAt x.1 x.2.1 x.2.2) ∗ K1 c
      = ownStr c.oldV ∗ (mapsto Mptr .Freeable c.smbcB (Integers.Ptrofs.unsigned c.smbcO) c.oldV
        ∗ (cP bp (.Vptr x.1 Integers.Ptrofs.zero) ∗ strAt x.1 x.2.1 x.2.2 ∗ cD c ∗ cR c c.reqV ∗ emp)) := by
    simp only [K1, cS]; ac_rfl
  refine triple_seq_fwd ge _ _ _
    (LocalSt (E bp) ((_t'23, c.oldV) :: Lk c)
      (mapsto Mptr .Freeable c.smbcB (Integers.Ptrofs.unsigned c.smbcO) c.oldV
        ∗ (cP bp (.Vptr x.1 Integers.Ptrofs.zero) ∗ strAt x.1 x.2.1 x.2.2 ∗ cD c ∗ cR c c.reqV ∗ emp))) _ _ _
    (triple_seq_fwd ge _ _ _
      (LocalSt (E bp) ((_t'23, c.oldV) :: Lk c) ((cP bp (.Vptr x.1 Integers.Ptrofs.zero)
        ∗ strAt x.1 x.2.1 x.2.2) ∗ K1 c)) _ _ _ ?a ?b) ?c
  case a =>
    refine set2 ge _ _ (E bp) _ _ _t'23 _ c.oldV (by lfresh) ?_
    intro le m hp hT hH hag
    exact eval_load (lv_share (b := c.smbcB) (o := c.smbcO) hcenv (hT.get (by lmem))) rfl
      (cell_load h1 hH hag hold)
  case b =>
    rw [h2]
    refine call_none ge _ _ freeSpec _ _ (E bp) _ (ownStr c.oldV) _ [c.oldV] bF fdF hF hfF htF ?hcl ?cal ?args
      (fun h hh => ⟨_, rfl, hh⟩) (fun _ _ hh => hh)
    case hcl => rfl
    case cal => exact fun _ _ _ => eval_callee_global (envP_other _ _ (by decide)) hsF rfl
    case args =>
      intro le m hT
      exact .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) (cast_ptr hold _ _ m) .nil
  case c =>
    refine triple_conseq ge _ _
      (assign_cell ge _ _ (E bp) _ _ _ _ Mptr c.smbcB c.smbcO _ c.oldV nullV rfl rfl ?lv ?ev)
      (fun _ _ _ x => x) (fun e le hp ⟨he, hT, hH⟩ => ⟨he, TempsHold_mono (by lsub) hT, hH⟩)
      (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
    case lv => exact fun le m hT => lv_share hcenv (hT.get (by lmem))
    case ev => exact fun le m hT => ⟨_, EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl, rfl⟩

theorem lift_ptr (ge fe f) (E : Env) (l : List (Ident × Val)) (v : Val) (K : HProp) (s : Stmt)
    (R : Sep.ExitConds) (h : IsPtr v → Triple ge fe f (LocalSt E l (ownStr v ∗ K)) s R) :
    Triple ge fe f (LocalSt E l (ownStr v ∗ K)) s R := by
  intro k e le hp hf m hd hag hP
  obtain ⟨he, hT, h1, h2, hd12, heq, hO, hK⟩ := hP
  exact h (ownStr_ptr hO) k e le hp hf m hd hag ⟨he, hT, h1, h2, hd12, heq, hO, hK⟩

abbrev H4 (c : Ctx) (bp : Block) (x : PS) (v4 : Val) : HProp :=
  cS c v4 ∗ ownStr v4 ∗ cP bp (.Vptr x.1 Integers.Ptrofs.zero) ∗ strAt x.1 x.2.1 x.2.2 ∗ cD c
    ∗ cR c c.reqV ∗ emp

def Q4 (c : Ctx) (bp : Block) : Sep.Assn := fun e le hp =>
  ∃ y : PS × Val, LocalSt (E bp) (Lk c) (H4 c bp y.1 y.2) e le hp

theorem path_eq (c : Ctx) (bp : Block) (x : PS) :
    H3 c bp x = cP bp (.Vptr x.1 Integers.Ptrofs.zero)
      ∗ (cS c nullV ∗ strAt x.1 x.2.1 x.2.2 ∗ cD c ∗ cR c c.reqV ∗ emp) := by
  unfold H3; ac_rfl

theorem str_eq (c : Ctx) (bp : Block) (x : PS) :
    H3 c bp x = strAt x.1 x.2.1 x.2.2
      ∗ (cS c nullV ∗ cP bp (.Vptr x.1 Integers.Ptrofs.zero) ∗ cD c ∗ cR c c.reqV ∗ emp) := by
  unfold H3; ac_rfl

/-- `(*path == '/' || *path == '\\') ? path + 1 : path` を `t'3` に入れる。 -/
theorem s4cond (ge : CGenv) (c : Ctx) (bp : Block) (x : PS) (A : Stmt)
    (hA : A = .Ssequence
      (.Ssequence (.Sset _t'19 (.Evar _path (tptr tschar)))
        (.Ssequence (.Sset _t'20 (.Ederef (.Etempvar _t'19 (tptr tschar)) tschar))
          (.Sifthenelse (.Ebinop .Oeq (.Etempvar _t'20 tschar) (.Econst_int (Integers.Int.repr 47) tint) tint)
            (.Sset _t'2 (.Econst_int (Integers.Int.repr 1) tint))
            (.Ssequence (.Sset _t'21 (.Evar _path (tptr tschar)))
              (.Ssequence (.Sset _t'22 (.Ederef (.Etempvar _t'21 (tptr tschar)) tschar))
                (.Sset _t'2 (.Ecast (.Ebinop .Oeq (.Etempvar _t'22 tschar)
                  (.Econst_int (Integers.Int.repr 92) tint) tint) tbool)))))))
      (.Sifthenelse (.Etempvar _t'2 tint)
        (.Ssequence (.Sset _t'18 (.Evar _path (tptr tschar)))
          (.Sset _t'3 (.Ecast (.Ebinop .Oadd (.Etempvar _t'18 (tptr tschar))
            (.Econst_int (Integers.Int.repr 1) tint) (tptr tschar)) (tptr tschar))))
        (.Ssequence (.Sset _t'17 (.Evar _path (tptr tschar)))
          (.Sset _t'3 (.Ecast (.Etempvar _t'17 (tptr tschar)) (tptr tschar)))))) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (LocalSt (E bp) (Lk c) (H3 c bp x)) A
      (.only (fun e le hp => ∃ v3, IsPtr v3 ∧ LocalSt (E bp) ((_t'3, v3) :: Lk c) (H3 c bp x) e le hp)) := by
  subst hA
  have hpv : IsPtr (.Vptr x.1 Integers.Ptrofs.zero) := Or.inl ⟨_, _, rfl⟩
  have hc0 : 0 ≤ x.2.2 := Nat.zero_le _
  refine triple_seq_fwd ge _ _ _
    (fun e le hp => ∃ bb : Bool, LocalSt (E bp) ((_t'2, Val.ofBool bb) :: Lk c) (H3 c bp x) e le hp)
    _ _ _ ?a1 ?a2
  case a1 =>
    refine triple_seq_fwd ge _ _ _
      (LocalSt (E bp) ((_t'19, .Vptr x.1 Integers.Ptrofs.zero) :: Lk c) (H3 c bp x)) _ _ _ ?b1 ?b2
    case b1 =>
      refine set2 ge _ _ (E bp) _ _ _t'19 _ _ (by lfresh) ?_
      intro le m hp hT hH hag
      exact eval_pathvar (path_eq c bp x) hH hag hpv
    case b2 =>
      refine triple_seq_fwd ge _ _ _
        (LocalSt (E bp) ((_t'20, .Vint (x.2.1 0)) :: (_t'19, .Vptr x.1 Integers.Ptrofs.zero) :: Lk c)
          (H3 c bp x)) _ _ _ ?d1 ?d2
      case d1 =>
        refine set2 ge _ _ (E bp) _ _ _t'20 _ _ (by lfresh) ?_
        intro le m hp hT hH hag
        exact eval_char_str (hT.get (by lmem)) unsigned_zero (str_eq c bp x) hH hag hc0
      case d2 =>
        refine triple_if_local ge _ _ (E bp) _ _ _ (Integers.Int.eq (x.2.1 0) (Integers.Int.repr 47)) _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) (EvalExpr.Econst_int _ _) (cmp47 _ _ m),
            boolVal_ofBool_tint _ m⟩) ?_
        cases h47 : Integers.Int.eq (x.2.1 0) (Integers.Int.repr 47)
        · -- '/' でない: t'21 = path; t'22 = *t'21; t'2 = (t'22 == '\\');
          refine triple_seq_fwd ge _ _ _
            (LocalSt (E bp) ((_t'21, .Vptr x.1 Integers.Ptrofs.zero) :: (_t'20, .Vint (x.2.1 0))
              :: (_t'19, .Vptr x.1 Integers.Ptrofs.zero) :: Lk c) (H3 c bp x)) _ _ _ ?e1 ?e2
          case e1 =>
            refine set2 ge _ _ (E bp) _ _ _t'21 _ _ (by lfresh) ?_
            intro le m hp hT hH hag
            exact eval_pathvar (path_eq c bp x) hH hag hpv
          case e2 =>
            refine triple_seq_fwd ge _ _ _
              (LocalSt (E bp) ((_t'22, .Vint (x.2.1 0)) :: (_t'21, .Vptr x.1 Integers.Ptrofs.zero)
                :: (_t'20, .Vint (x.2.1 0)) :: (_t'19, .Vptr x.1 Integers.Ptrofs.zero) :: Lk c)
                (H3 c bp x)) _ _ _ ?f1 ?f2
            case f1 =>
              refine set2 ge _ _ (E bp) _ _ _t'22 _ _ (by lfresh) ?_
              intro le m hp hT hH hag
              exact eval_char_str (hT.get (by lmem)) unsigned_zero (str_eq c bp x) hH hag hc0
            case f2 =>
              refine triple_conseq ge _ _
                (set2 ge _ _ (E bp) _ _ _t'2 _ (Val.ofBool (Integers.Int.eq (x.2.1 0) (Integers.Int.repr 92)))
                  (by lfresh) ?_) (fun _ _ _ x => x)
                (fun e le hp ⟨he, hT, hH⟩ => ⟨_, he, TempsHold_mono (by lsub) hT, hH⟩)
                (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
              intro le m hp hT _ _
              exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _
                (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) (EvalExpr.Econst_int _ _) (cmp92 _ _ m))
                (cast_bool _ m)
        · -- '/': t'2 = 1;
          refine triple_conseq ge _ _ (set2 ge _ _ (E bp) _ _ _t'2 _ (Val.ofBool true) (by lfresh) ?_)
            (fun _ _ _ x => x)
            (fun e le hp ⟨he, hT, hH⟩ => ⟨true, he, TempsHold_mono (by lsub) hT, hH⟩)
            (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
          intro le m hp hT _ _
          exact EvalExpr.Econst_int _ _
  case a2 =>
    refine triple_lift ge _ _ (fun bb : Bool => LocalSt (E bp) ((_t'2, Val.ofBool bb) :: Lk c) (H3 c bp x))
      _ _ _ (fun e le hp h => h) ?_
    intro bb
    refine triple_if_local ge _ _ (E bp) _ _ _ bb _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by lmem)), boolVal_ofBool_tint _ m⟩) ?_
    cases bb
    · refine triple_seq_fwd ge _ _ _
        (LocalSt (E bp) ((_t'17, .Vptr x.1 Integers.Ptrofs.zero) :: (_t'2, Val.ofBool false) :: Lk c)
          (H3 c bp x)) _ _ _ ?h1 ?h2
      case h1 =>
        refine set2 ge _ _ (E bp) _ _ _t'17 _ _ (by lfresh) ?_
        intro le m hp hT hH hag
        exact eval_pathvar (path_eq c bp x) hH hag hpv
      case h2 =>
        refine triple_conseq ge _ _ (set2 ge _ _ (E bp) _ _ _t'3 _ (.Vptr x.1 Integers.Ptrofs.zero) (by lfresh) ?_)
          (fun _ _ _ x => x)
          (fun e le hp ⟨he, hT, hH⟩ => ⟨_, hpv, he, TempsHold_mono (by lsub) hT, hH⟩)
          (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
        intro le m hp hT _ _
        exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) (cast_ptr hpv _ _ m)
    · refine triple_seq_fwd ge _ _ _
        (LocalSt (E bp) ((_t'18, .Vptr x.1 Integers.Ptrofs.zero) :: (_t'2, Val.ofBool true) :: Lk c)
          (H3 c bp x)) _ _ _ ?h1 ?h2
      case h1 =>
        refine set2 ge _ _ (E bp) _ _ _t'18 _ _ (by lfresh) ?_
        intro le m hp hT hH hag
        exact eval_pathvar (path_eq c bp x) hH hag hpv
      case h2 =>
        refine triple_conseq ge _ _ (set2 ge _ _ (E bp) _ _ _t'3 _
            (.Vptr x.1 (Integers.Ptrofs.add Integers.Ptrofs.zero
              (Integers.Ptrofs.mul (Integers.Ptrofs.repr (sizeof ge.genv_cenv tschar))
                (Cop.ptrofsOfInt .Signed (Integers.Int.repr 1))))) (by lfresh) ?_)
          (fun _ _ _ x => x)
          (fun e le hp ⟨he, hT, hH⟩ => ⟨_, Or.inl ⟨_, _, rfl⟩, he, TempsHold_mono (by lsub) hT, hH⟩)
          (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
        intro le m hp hT _ _
        exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) (EvalExpr.Econst_int _ _)
          (semAdd_ptr_int _ _ _ _ _ rfl)) (cast_ptr (Or.inl ⟨_, _, rfl⟩) _ _ m)

theorem s4 (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx) (X : Ext ge) (bp : Block) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (Q3 c bp) hd3 (RR (ppPostA c) (Q4 c bp)) := by
  obtain ⟨bD, fdD, hsD, hfD, htD, hD⟩ := X.dup
  refine only_RR _ _ _ _ ?_
  refine triple_lift ge _ _ (fun x : PS => LocalSt (E bp) (Lk c) (H3 c bp x)) _ _ _ (fun e le hp h => h) ?_
  intro x
  refine triple_seq_fwd ge _ _ _
    (fun e le hp => ∃ v4, LocalSt (E bp) ((_t'4, v4) :: Lk c) (ownStr v4 ∗ H3 c bp x) e le hp) _ _ _ ?a ?b
  case a =>
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (s4cond ge c bp x _ rfl) ?_
    refine triple_lift ge _ _ (fun v3 : Val => fun e le hp => IsPtr v3
        ∧ LocalSt (E bp) ((_t'3, v3) :: Lk c) (H3 c bp x) e le hp) _ _ _ (fun e le hp h => h) ?_
    intro v3
    refine Case1C.triple_pure ge _ _ _ _ _ _ ?_
    intro hv3
    refine heap_eq ge _ _ _ _ _ (emp ∗ H3 c bp x) _ _ (emp_sep_eq _).symm ?_
    refine triple_conseq ge _ _
      (call2 ge _ _ dupSpec _t'4 _ _ (E bp) _ emp (H3 c bp x) [v3] bD fdD hD hfD htD ?hcl (by lfresh) ?cal ?args
        (fun h hh => hh))
      (fun _ _ _ x => x) (fun e le hp ⟨v, he, hT, hH⟩ => ⟨v, he, TempsHold_mono (by lsub) hT, hH⟩)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
    case hcl => rfl
    case cal => exact fun _ _ _ => eval_callee_global (envP_other _ _ (by decide)) hsD rfl
    case args =>
      intro le m hT
      exact .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) (cast_ptr hv3 _ _ m) .nil
  case b =>
    refine triple_lift ge _ _ (fun v4 : Val => LocalSt (E bp) ((_t'4, v4) :: Lk c) (ownStr v4 ∗ H3 c bp x)) _ _ _
      (fun e le hp h => h) ?_
    intro v4
    refine lift_ptr ge _ _ (E bp) _ v4 _ _ _ ?_
    intro hv4
    have he : ownStr v4 ∗ H3 c bp x
        = mapsto Mptr .Freeable c.smbcB (Integers.Ptrofs.unsigned c.smbcO) nullV
          ∗ (ownStr v4 ∗ cP bp (.Vptr x.1 Integers.Ptrofs.zero) ∗ strAt x.1 x.2.1 x.2.2 ∗ cD c
             ∗ cR c c.reqV ∗ emp) := by
      simp only [H3, cS]; ac_rfl
    rw [he]
    refine triple_conseq ge _ _
      (assign_cell ge _ _ (E bp) _ _ _ _ Mptr c.smbcB c.smbcO _ nullV v4 rfl rfl ?lv ?ev)
      (fun _ _ _ x => x) (fun e le hp ⟨he, hT, hH⟩ => ⟨(x, v4), he, TempsHold_mono (by lsub) hT, ?hh⟩)
      (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
    case lv => exact fun le m hT => lv_share hcenv (hT.get (by lmem))
    case ev => exact fun le m hT => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by lmem)), cast_ptr hv4 _ _ m⟩
    case hh =>
      have he2 : H4 c bp x v4 = mapsto Mptr .Freeable c.smbcB (Integers.Ptrofs.unsigned c.smbcO) v4
          ∗ (ownStr v4 ∗ cP bp (.Vptr x.1 Integers.Ptrofs.zero) ∗ strAt x.1 x.2.1 x.2.2 ∗ cD c
             ∗ cR c c.reqV ∗ emp) := by
        simp only [H4, cS]
      show H4 c bp x v4 hp
      rw [he2]; exact hH

abbrev H5 (c : Ctx) (bp : Block) (v4 : Val) : HProp :=
  cS c v4 ∗ ownStr v4 ∗ cR c c.reqV ∗ cD c ∗ Case3C.Locs [(bp, 8)]

def Q5 (c : Ctx) (bp : Block) : Sep.Assn := fun e le hp =>
  ∃ v4 : Val, LocalSt (E bp) (Lk c) (H5 c bp v4) e le hp

theorem s5 (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx) (X : Ext ge) (bp : Block) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (Q4 c bp) hd4 (RR (ppPostA c) (Q5 c bp)) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.free
  refine only_RR _ _ _ _ ?_
  refine triple_lift ge _ _ (fun y : PS × Val => LocalSt (E bp) (Lk c) (H4 c bp y.1 y.2)) _ _ _
    (fun e le hp h => h) ?_
  intro ⟨x, v4⟩
  have hpv : IsPtr (.Vptr x.1 Integers.Ptrofs.zero) := Or.inl ⟨_, _, rfl⟩
  have hp1 : H4 c bp x v4 = cP bp (.Vptr x.1 Integers.Ptrofs.zero)
      ∗ (cS c v4 ∗ ownStr v4 ∗ strAt x.1 x.2.1 x.2.2 ∗ cD c ∗ cR c c.reqV ∗ emp) := by
    unfold H4; ac_rfl
  have hp2 : H4 c bp x v4 = strAt x.1 x.2.1 x.2.2
      ∗ (cS c v4 ∗ ownStr v4 ∗ cP bp (.Vptr x.1 Integers.Ptrofs.zero) ∗ cD c ∗ cR c c.reqV ∗ emp) := by
    unfold H4; ac_rfl
  refine triple_seq_fwd ge _ _ _
    (LocalSt (E bp) ((_t'16, .Vptr x.1 Integers.Ptrofs.zero) :: Lk c) (H4 c bp x v4)) _ _ _ ?a ?b
  case a =>
    refine set2 ge _ _ (E bp) _ _ _t'16 _ _ (by lfresh) ?_
    intro le m hp hT hH hag
    exact eval_pathvar hp1 hH hag hpv
  case b =>
    rw [hp2]
    refine triple_conseq ge _ _
      (call_none ge _ _ freeSpec _ _ (E bp) _ (strAt x.1 x.2.1 x.2.2) _ [.Vptr x.1 Integers.Ptrofs.zero]
        bF fdF hF hfF htF ?hcl ?cal ?args
        (fun h hh => ⟨_, rfl, Or.inr ⟨x.1, x.2.1, x.2.2, rfl, hh⟩⟩) (fun _ _ hh => hh))
      (fun _ _ _ x => x) (fun e le hp ⟨he, hT, hH⟩ => ⟨v4, he, TempsHold_mono (by lsub) hT, ?hh⟩)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
    case hcl => rfl
    case cal => exact fun _ _ _ => eval_callee_global (envP_other _ _ (by decide)) hsF rfl
    case args =>
      intro le m hT
      exact .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) (cast_ptr hpv _ _ m) .nil
    case hh =>
      have h5 : H5 c bp v4 = cS c v4 ∗ ownStr v4 ∗ anyBytes .Freeable bp 0 8 ∗ cD c ∗ cR c c.reqV ∗ emp := by
        simp only [H5, Case3C.Locs]; ac_rfl
      show H5 c bp v4 hp
      rw [h5]
      exact sep_mono (entails_refl _) (sep_mono (entails_refl _)
        (sep_mono (fun h hh => mapsto_any hh) (entails_refl _))) _ hH

theorem lift_and (ge fe f) (E : Env) (l : List (Ident × Val)) (φ : Prop) (A K : HProp) (s : Stmt)
    (R : Sep.ExitConds) (h : φ → Triple ge fe f (LocalSt E l (A ∗ K)) s R) :
    Triple ge fe f (LocalSt E l ((fun hp => φ ∧ A hp) ∗ K)) s R := by
  intro k e le hp hf m hd hag hP
  obtain ⟨he, hT, h1, h2, hd12, heq, ⟨hφ, hA⟩, hK⟩ := hP
  exact h hφ k e le hp hf m hd hag ⟨he, hT, h1, h2, hd12, heq, hA, hK⟩

/-- `ownStr v ∗ K` を、NULL の場合とブロックの場合に分ける。 -/
theorem lift_own (ge fe f) (E : Env) (l : List (Ident × Val)) (v : Val) (K : HProp) (s : Stmt)
    (R : Sep.ExitConds)
    (hn : v = nullV → Triple ge fe f (LocalSt E l (emp ∗ K)) s R)
    (hs : ∀ x : PS, v = .Vptr x.1 Integers.Ptrofs.zero →
      Triple ge fe f (LocalSt E l (strAt x.1 x.2.1 x.2.2 ∗ K)) s R) :
    Triple ge fe f (LocalSt E l (ownStr v ∗ K)) s R := by
  intro k e le hp hf m hd hag hP
  obtain ⟨he, hT, h1, h2, hd12, heq, hO, hK⟩ := hP
  rcases hO with ⟨hv, hE⟩ | ⟨b, f', n, hv, hS⟩
  · exact hn hv k e le hp hf m hd hag ⟨he, hT, h1, h2, hd12, heq, hE, hK⟩
  · exact hs (b, f', n) hv k e le hp hf m hd hag ⟨he, hT, h1, h2, hd12, heq, hS, hK⟩

abbrev H6 (c : Ctx) (bp : Block) (x : PS) : HProp :=
  cS c (.Vptr x.1 Integers.Ptrofs.zero) ∗ strAt x.1 x.2.1 x.2.2 ∗ cR c c.reqV ∗ cD c
    ∗ Case3C.Locs [(bp, 8)]

def Q6 (c : Ctx) (bp : Block) : Sep.Assn := fun e le hp =>
  ∃ x : PS, LocalSt (E bp) (Lk c) (H6 c bp x) e le hp

theorem post27 (c : Ctx) (hp : Heap) : ppPostA c (.Vint (Integers.Int.repr 27)) hp :=
  post_err c _ (by decide) hp

theorem s6 (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx) (bp : Block) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (Q5 c bp) hd5 (RR (ppPostA c) (Q6 c bp)) := by
  refine triple_lift ge _ _ (fun v4 : Val => LocalSt (E bp) (Lk c) (H5 c bp v4)) _ _ _
    (fun e le hp h => h) ?_
  intro v4
  have h1 : H5 c bp v4 = ownStr v4 ∗ (cS c v4 ∗ cR c c.reqV ∗ cD c ∗ Case3C.Locs [(bp, 8)]) := by
    unfold H5; ac_rfl
  rw [h1]
  refine lift_ptr ge _ _ (E bp) _ v4 _ _ _ ?_
  intro hv4
  have h2 : ownStr v4 ∗ (cS c v4 ∗ cR c c.reqV ∗ cD c ∗ Case3C.Locs [(bp, 8)])
      = mapsto Mptr .Freeable c.smbcB (Integers.Ptrofs.unsigned c.smbcO) v4
        ∗ (ownStr v4 ∗ cR c c.reqV ∗ cD c ∗ Case3C.Locs [(bp, 8)]) := by
    unfold cS; ac_rfl
  refine triple_seq_fwd ge _ _ _ (LocalSt (E bp) ((_t'15, v4) :: Lk c)
    (ownStr v4 ∗ (cS c v4 ∗ cR c c.reqV ∗ cD c ∗ Case3C.Locs [(bp, 8)]))) _ _ _ ?a ?b
  case a =>
    refine set2 ge _ _ (E bp) _ _ _t'15 _ _ (by lfresh) ?_
    intro le m hp hT hH hag
    exact eval_load (lv_share (b := c.smbcB) (o := c.smbcO) hcenv (hT.get (by lmem))) rfl
      (cell_load h2 hH hag hv4)
  case b =>
    refine lift_own ge _ _ (E bp) _ v4 _ _ _ ?n ?s
    case n =>
      intro hv; subst hv
      refine triple_if_local ge _ _ (E bp) _ _ _ true _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem)))
          notbool_null, boolVal_ofBool_tint _ m⟩) ?_
      have h3 : emp ∗ (cS c nullV ∗ cR c c.reqV ∗ cD c ∗ Case3C.Locs [(bp, 8)])
          = (emp ∗ cS c nullV ∗ cR c c.reqV ∗ cD c) ∗ Case3C.Locs [(bp, 8)] := by ac_rfl
      rw [h3]
      exact ret_here ge _ _ hcenv bp _ _ _ _ _ _ _ (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)
        (fun _ => rfl) (fun hp _ => post27 c hp)
    case s =>
      intro x hv; subst hv
      have h4 : strAt x.1 x.2.1 x.2.2 ∗ (cS c (.Vptr x.1 Integers.Ptrofs.zero) ∗ cR c c.reqV ∗ cD c
          ∗ Case3C.Locs [(bp, 8)]) = strAt x.1 x.2.1 x.2.2 ∗ (cS c (.Vptr x.1 Integers.Ptrofs.zero)
          ∗ cR c c.reqV ∗ cD c ∗ Case3C.Locs [(bp, 8)]) := rfl
      refine triple_if_local ge _ _ (E bp) _ _ _ false _ _ _ ?_ ?_
      · intro le m hp hT hH hag
        refine ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem)))
          (notbool_ptr ?_), boolVal_ofBool_tint _ m⟩
        rw [unsigned_zero]
        exact valid_str h4 hH hag (Nat.zero_le _)
      · exact triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x)
          (fun e le hp ⟨he, hT, hH⟩ => ⟨x, he, TempsHold_mono (by lsub) hT, by
            show H6 c bp x hp; unfold H6; rw [show (strAt x.1 x.2.1 x.2.2 ∗ cS c (.Vptr x.1 Integers.Ptrofs.zero)
              ∗ cR c c.reqV ∗ cD c ∗ Case3C.Locs [(bp, 8)]) = (cS c (.Vptr x.1 Integers.Ptrofs.zero)
              ∗ strAt x.1 x.2.1 x.2.2 ∗ cR c c.reqV ∗ cD c ∗ Case3C.Locs [(bp, 8)]) by ac_rfl] at hH
            exact hH⟩)
          (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)

def phi7 (x : PS) (w : Val) : Prop :=
  w = nullV ∨ ∃ k o, k < x.2.2 ∧ Integers.Ptrofs.unsigned o = (k : _root_.Int) ∧ w = .Vptr x.1 o

def Q7 (c : Ctx) (bp : Block) : Sep.Assn := fun e le hp =>
  ∃ y : PS × Val, phi7 y.1 y.2 ∧ LocalSt (E bp) ((_slash, y.2) :: Lk c) (H6 c bp y.1) e le hp

theorem shareH6 (c : Ctx) (bp : Block) (x : PS) :
    H6 c bp x = mapsto Mptr .Freeable c.smbcB (Integers.Ptrofs.unsigned c.smbcO) (.Vptr x.1 Integers.Ptrofs.zero)
      ∗ (strAt x.1 x.2.1 x.2.2 ∗ cR c c.reqV ∗ cD c ∗ Case3C.Locs [(bp, 8)]) := by
  unfold H6 cS; ac_rfl

theorem strH6 (c : Ctx) (bp : Block) (x : PS) :
    H6 c bp x = strAt x.1 x.2.1 x.2.2
      ∗ (cS c (.Vptr x.1 Integers.Ptrofs.zero) ∗ cR c c.reqV ∗ cD c ∗ Case3C.Locs [(bp, 8)]) := by
  unfold H6; ac_rfl

/-- `t = smbc->share; u = strchr(t, ch); slash = u;`（`ch` は '/' か '\\'） -/
theorem chr_step (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx) (X : Ext ge)
    (bp : Block) (x : PS) (l : List (Ident × Val)) (t u : Ident) (ch : Integers.Int)
    (hlt : ∀ q ∈ l, q.1 ≠ t) (hlu : ∀ q ∈ (t, Val.Vptr x.1 Integers.Ptrofs.zero) :: l, q.1 ≠ u)
    (hls : (_smbc, Val.Vptr c.smbcB c.smbcO) ∈ l) (hLk : ∀ q ∈ Lk c, q ∈ l)
    (S : Stmt)
    (hS : S = .Ssequence (.Ssequence (.Sset t shareE)
      (.Scall (some u) (.Evar _strchr (Ty.Tfunction [tptr tschar, tint] (tptr tschar) cc_default))
        [.Etempvar t (tptr tschar), .Econst_int ch tint]))
      (.Sset _slash (.Etempvar u (tptr tschar)))) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (LocalSt (E bp) l (H6 c bp x)) S
      (.only (fun e le hp => ∃ w, phi7 x w ∧ LocalSt (E bp) ((_slash, w) :: Lk c) (H6 c bp x) e le hp)) := by
  subst hS
  obtain ⟨bC, fdC, hsC, hfC, htC, hC⟩ := X.chr
  have hpv : IsPtr (.Vptr x.1 Integers.Ptrofs.zero) := Or.inl ⟨_, _, rfl⟩
  refine triple_seq_fwd ge _ _ _
    (fun e le hp => ∃ w, phi7 x w ∧ LocalSt (E bp) ((u, w) :: (t, Val.Vptr x.1 Integers.Ptrofs.zero) :: l)
      (H6 c bp x) e le hp) _ _ _ ?a ?b
  case a =>
    refine triple_seq_fwd ge _ _ _ (LocalSt (E bp) ((t, Val.Vptr x.1 Integers.Ptrofs.zero) :: l) (H6 c bp x))
      _ _ _ ?a1 ?a2
    case a1 =>
      refine set2 ge _ _ (E bp) _ _ t _ _ hlt ?_
      intro le m hp hT hH hag
      exact eval_load (lv_share (b := c.smbcB) (o := c.smbcO) hcenv (hT.get hls)) rfl
        (cell_load (shareH6 c bp x) hH hag hpv)
    case a2 =>
      rw [strH6 c bp x]
      refine triple_conseq ge _ _
        (call2 ge _ _ (chrSpec x.1 x.2.1 x.2.2) u _ _ (E bp) _ (strAt x.1 x.2.1 x.2.2) _
          [.Vptr x.1 Integers.Ptrofs.zero, .Vint ch] bC fdC (hC x.1 x.2.1 x.2.2) hfC htC ?hcl hlu ?cal ?args
          (fun h hh => ⟨⟨_, rfl⟩, hh⟩))
        (fun _ _ _ x => x) ?n (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
      case hcl => rfl
      case cal => exact fun _ _ _ => eval_callee_global (envP_other _ _ (by decide)) hsC rfl
      case args =>
        intro le m hT
        exact .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..)))
          (cast_ptr hpv _ _ m) (.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl .nil)
      case n =>
        intro e le hp ⟨w, he, hT, h1, h2, hd, heq, hpost, hK⟩
        obtain ⟨hφ, hst⟩ := pure_sep_elim hpost
        exact ⟨w, hφ, he, hT, h1, h2, hd, heq, hst, hK⟩
  case b =>
    refine triple_lift ge _ _ (fun w : Val => fun e le hp => phi7 x w ∧ LocalSt (E bp)
      ((u, w) :: (t, Val.Vptr x.1 Integers.Ptrofs.zero) :: l) (H6 c bp x) e le hp) _ _ _
      (fun e le hp h => h) ?_
    intro w
    refine Case1C.triple_pure ge _ _ _ _ _ _ ?_
    intro hφ
    refine triple_conseq ge _ _ (triple_set_local ge _ _ (E bp) _ (Lk c) _ _slash _ w
        (fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hLk q hq))) (by lfresh) ?_)
      (fun _ _ _ x => x)
      (fun e le hp h => ⟨w, hφ, h⟩) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
    intro le m hp hT _ _
    exact EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..))

theorem s7 (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx) (X : Ext ge) (bp : Block) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (Q6 c bp) hd6 (RR (ppPostA c) (Q7 c bp)) := by
  refine only_RR _ _ _ _ ?_
  refine triple_lift ge _ _ (fun x : PS => LocalSt (E bp) (Lk c) (H6 c bp x)) _ _ _ (fun e le hp h => h) ?_
  intro x
  exact triple_conseq ge _ _
    (chr_step ge hcenv c X bp x (Lk c) _t'14 _t'5 (Integers.Int.repr 47) (by lfresh) (by lfresh) (by lmem)
      (fun _ h => h) _ rfl)
    (fun _ _ _ x => x) (fun e le hp ⟨w, hφ, h⟩ => ⟨(x, w), hφ, h⟩)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

theorem valid_slash {c : Ctx} {bp : Block} {x : PS} {o : Integers.Ptrofs} {k : Nat} {hp : Heap} {m : Mem}
    (hH : H6 c bp x hp) (hag : Heap.Agrees hp m) (hk : k < x.2.2) (ho : Integers.Ptrofs.unsigned o = k) :
    Cop.semUnaryOperation .Onotbool (.Vptr x.1 o) (tptr tschar) m = some (Val.ofBool false) := by
  refine notbool_ptr ?_
  rw [ho]
  exact valid_str (strH6 c bp x) hH hag (Nat.le_of_lt hk)

theorem s8 (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx) (X : Ext ge) (bp : Block) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (Q7 c bp) hd7 (RR (ppPostA c) (Q7 c bp)) := by
  refine only_RR _ _ _ _ ?_
  refine triple_lift ge _ _ (fun y : PS × Val => fun e le hp => phi7 y.1 y.2
    ∧ LocalSt (E bp) ((_slash, y.2) :: Lk c) (H6 c bp y.1) e le hp) _ _ _ (fun e le hp h => h) ?_
  intro ⟨x, w⟩
  refine Case1C.triple_pure ge _ _ _ _ _ _ ?_
  intro hφ
  dsimp only at hφ ⊢
  rcases hφ with hn | ⟨k, o, hk, ho, hw⟩
  · subst hn
    refine triple_if_local ge _ _ (E bp) _ _ _ true _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem)))
        notbool_null, boolVal_ofBool_tint _ m⟩) ?_
    exact triple_conseq ge _ _
      (chr_step ge hcenv c X bp x ((_slash, nullV) :: Lk c) _t'13 _t'6 (Integers.Int.repr 92)
        (by lfresh) (by lfresh) (by lmem) (fun q h => List.mem_cons_of_mem _ h) _ rfl)
      (fun _ _ _ x => x) (fun e le hp ⟨w', hφ, h⟩ => ⟨(x, w'), hφ, h⟩)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
  · subst hw
    refine triple_if_local ge _ _ (E bp) _ _ _ false _ _ _
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem)))
        (valid_slash hH hag hk ho), boolVal_ofBool_tint _ m⟩) ?_
    exact triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x)
      (fun e le hp h => ⟨(x, .Vptr x.1 o), Or.inr ⟨k, o, hk, ho, rfl⟩, h⟩)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

def Q9 (c : Ctx) (bp : Block) : Sep.Assn := fun e le hp =>
  ∃ y : PS × Nat × Integers.Ptrofs, y.2.1 < y.1.2.2 ∧ Integers.Ptrofs.unsigned y.2.2 = (y.2.1 : _root_.Int)
    ∧ LocalSt (E bp) ((_slash, .Vptr y.1.1 y.2.2) :: Lk c) (H6 c bp y.1) e le hp

theorem post3 (c : Ctx) (hp : Heap) : ppPostA c (.Vint (Integers.Int.repr 3)) hp :=
  post_err c _ (by decide) hp

theorem s9 (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx) (X : Ext ge) (bp : Block) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (Q7 c bp) hd8 (RR (ppPostA c) (Q9 c bp)) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.free
  obtain ⟨bL, fdL, hsL, hfL, htL, hL⟩ := X.fail
  obtain ⟨bS, hsS⟩ := X.lit
  refine triple_lift ge _ _ (fun y : PS × Val => fun e le hp => phi7 y.1 y.2
    ∧ LocalSt (E bp) ((_slash, y.2) :: Lk c) (H6 c bp y.1) e le hp) _ _ _ (fun e le hp h => h) ?_
  intro ⟨x, w⟩
  refine Case1C.triple_pure ge _ _ _ _ _ _ ?_
  intro hφ
  dsimp only at hφ ⊢
  have hpv : IsPtr (.Vptr x.1 Integers.Ptrofs.zero) := Or.inl ⟨_, _, rfl⟩
  rcases hφ with hn | ⟨k, o, hk, ho, hw⟩
  · subst hn
    refine triple_if_local ge _ _ (E bp) _ _ _ true _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem)))
        notbool_null, boolVal_ofBool_tint _ m⟩) ?_
    refine triple_seq ge _ _ _
      (LocalSt (E bp) ((_slash, nullV) :: Lk c)
        (cS c nullV ∗ (cR c c.reqV ∗ cD c ∗ Case3C.Locs [(bp, 8)]))) _ _ _ ?a ?b
    case a =>
      refine only_RR _ _ _ _ (once_loop ge _ _ _ _ _ ?_)
      refine triple_seq_fwd ge _ _ _
        (LocalSt (E bp) ((_t'12, .Vptr x.1 Integers.Ptrofs.zero) :: (_slash, nullV) :: Lk c)
          (cS c (.Vptr x.1 Integers.Ptrofs.zero) ∗ (cR c c.reqV ∗ cD c ∗ Case3C.Locs [(bp, 8)]))) _ _ _
        (triple_seq_fwd ge _ _ _
          (LocalSt (E bp) ((_t'12, .Vptr x.1 Integers.Ptrofs.zero) :: (_slash, nullV) :: Lk c) (H6 c bp x))
          _ _ _ ?a1 ?a2) ?a3
      case a1 =>
        refine set2 ge _ _ (E bp) _ _ _t'12 _ _ (by lfresh) ?_
        intro le m hp hT hH hag
        exact eval_load (lv_share (b := c.smbcB) (o := c.smbcO) hcenv (hT.get (by lmem))) rfl
          (cell_load (shareH6 c bp x) hH hag hpv)
      case a2 =>
        rw [strH6 c bp x]
        refine call_none ge _ _ freeSpec _ _ (E bp) _ (strAt x.1 x.2.1 x.2.2) _ [.Vptr x.1 Integers.Ptrofs.zero]
          bF fdF hF hfF htF ?hcl ?cal ?args
          (fun h hh => ⟨_, rfl, Or.inr ⟨x.1, x.2.1, x.2.2, rfl, hh⟩⟩) (fun _ _ hh => hh)
        case hcl => rfl
        case cal => exact fun _ _ _ => eval_callee_global (envP_other _ _ (by decide)) hsF rfl
        case args =>
          intro le m hT
          exact .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) (cast_ptr hpv _ _ m) .nil
      case a3 =>
        refine triple_conseq ge _ _
          (assign_cell ge _ _ (E bp) _ _ _ _ Mptr c.smbcB c.smbcO _ _ nullV rfl rfl ?lv ?ev)
          (fun _ _ _ x => x) (fun e le hp ⟨he, hT, hH⟩ => ⟨he, TempsHold_mono (by lsub) hT, hH⟩)
          (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
        case lv => exact fun le m hT => lv_share hcenv (hT.get (by lmem))
        case ev => exact fun le m hT => ⟨_, EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl, rfl⟩
    case b =>
      rw [← emp_sep_eq (cS c nullV ∗ (cR c c.reqV ∗ cD c ∗ Case3C.Locs [(bp, 8)]))]
      refine triple_seq ge _ _ _
        (LocalSt (E bp) ((_slash, nullV) :: Lk c)
          (cS c nullV ∗ (cR c c.reqV ∗ cD c ∗ Case3C.Locs [(bp, 8)]))) _ _ _ ?c1 ?c2
      case c1 =>
        refine only_RR _ _ _ _ ?_
        refine call_none ge _ _ failSpec _ _ (E bp) _ emp _
          [.Vptr c.dataB c.dataO, .Vptr bS Integers.Ptrofs.zero] bL fdL hL hfL htL ?hcl ?cal ?args
          (fun h hh => hh) (fun _ _ hh => hh)
        case hcl => rfl
        case cal => exact fun _ _ _ => eval_callee_global (envP_other _ _ (by decide)) hsL rfl
        case args =>
          intro le m hT
          exact .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) rfl
            (.cons _ _ _ _ _ _ _ (eval_callee_global (envP_other _ _ (by decide)) hsS rfl) rfl .nil)
      case c2 =>
        have h3 : cS c nullV ∗ (cR c c.reqV ∗ cD c ∗ Case3C.Locs [(bp, 8)])
            = (cS c nullV ∗ cR c c.reqV ∗ cD c) ∗ Case3C.Locs [(bp, 8)] := by ac_rfl
        rw [h3]
        exact ret_here ge _ _ hcenv bp _ _ _ _ _ _ _ (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)
          (fun _ => rfl) (fun hp _ => post3 c hp)
  · subst hw
    refine triple_if_local ge _ _ (E bp) _ _ _ false _ _ _
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem)))
        (valid_slash hH hag hk ho), boolVal_ofBool_tint _ m⟩) ?_
    exact triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x)
      (fun e le hp h => ⟨(x, k, o), hk, ho, h⟩)
      (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)

abbrev R6 (c : Ctx) (bp : Block) (x : PS) : HProp :=
  cS c (.Vptr x.1 Integers.Ptrofs.zero) ∗ cR c c.reqV ∗ cD c ∗ Case3C.Locs [(bp, 8)]

theorem H6_split (c : Ctx) (bp : Block) (x : PS) :
    H6 c bp x = (⌜Tail x.2.1 0 x.2.2⌝ ∗ arr x.1 x.2.1 (x.2.2 + 1)) ∗ R6 c bp x := by
  unfold H6 R6 strAt; ac_rfl

def inc1 (ce : CompositeEnv) (o : Integers.Ptrofs) : Integers.Ptrofs :=
  Integers.Ptrofs.add o (Integers.Ptrofs.mul (Integers.Ptrofs.repr (sizeof ce tschar))
    (Cop.ptrofsOfInt .Signed (Integers.Int.repr 1)))

def Q10 (c : Ctx) (bp : Block) (ce : CompositeEnv) : Sep.Assn := fun e le hp =>
  ∃ y : PS × Nat × Integers.Ptrofs, y.2.1 < y.1.2.2 ∧ Integers.Ptrofs.unsigned y.2.2 = (y.2.1 : _root_.Int)
    ∧ Tail y.1.2.1 0 y.1.2.2
    ∧ LocalSt (E bp) ((_slash, .Vptr y.1.1 (inc1 ce y.2.2)) :: Lk c)
        (arr y.1.1 (upd y.1.2.1 y.2.1 Integers.Int.zero) (y.1.2.2 + 1) ∗ R6 c bp y.1) e le hp

theorem s10 (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx) (bp : Block) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (Q9 c bp) hd9
      (RR (ppPostA c) (Q10 c bp ge.genv_cenv)) := by
  refine only_RR _ _ _ _ ?_
  refine triple_lift ge _ _ (fun y : PS × Nat × Integers.Ptrofs => fun e le hp => y.2.1 < y.1.2.2
    ∧ Integers.Ptrofs.unsigned y.2.2 = (y.2.1 : _root_.Int)
    ∧ LocalSt (E bp) ((_slash, .Vptr y.1.1 y.2.2) :: Lk c) (H6 c bp y.1) e le hp) _ _ _
    (fun e le hp h => h) ?_
  intro ⟨x, k, o⟩
  refine triple_lift ge _ _ (fun (_ : k < x.2.2 ∧ Integers.Ptrofs.unsigned o = (k : _root_.Int)) =>
    LocalSt (E bp) ((_slash, .Vptr x.1 o) :: Lk c) (H6 c bp x)) _ _ _
    (fun e le hp ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩) ?_
  intro ⟨hk, ho⟩
  rw [H6_split c bp x]
  refine lift_pure ge _ _ (E bp) _ _ _ _ _ _ ?_
  intro ht
  refine triple_seq_fwd ge _ _ _
    (LocalSt (E bp) ((_slash, .Vptr x.1 (inc1 ge.genv_cenv o)) :: (_t'7, .Vptr x.1 o) :: Lk c)
      (arr x.1 x.2.1 (x.2.2 + 1) ∗ R6 c bp x)) _ _ _
    (triple_seq_fwd ge _ _ _
      (LocalSt (E bp) ((_t'7, .Vptr x.1 o) :: (_slash, .Vptr x.1 o) :: Lk c)
        (arr x.1 x.2.1 (x.2.2 + 1) ∗ R6 c bp x)) _ _ _ ?a ?b) ?c
  case a =>
    refine set2 ge _ _ (E bp) _ _ _t'7 _ _ (by lfresh) ?_
    intro le m hp hT _ _
    exact EvalExpr.Etempvar _ _ _ (hT.get (by lmem))
  case b =>
    refine triple_set_local ge _ _ (E bp) _ ((_t'7, .Vptr x.1 o) :: Lk c) _ _slash _ _ (by lsub) (by lfresh) ?_
    intro le m hp hT _ _
    exact EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) (EvalExpr.Econst_int _ _)
      (semAdd_ptr_int _ _ _ _ _ rfl)
  case c =>
    refine triple_conseq ge _ _
      (assign_byte ge _ _ (E bp) _ _ _ _ x.1 o x.2.1 (x.2.2 + 1) k Integers.Int.zero (by omega) rfl ho ?lv ?ev)
      (fun _ _ _ x => x) (fun e le hp ⟨he, hT, hH⟩ => ⟨(x, k, o), hk, ho, ht, he,
        TempsHold_mono (by lsub) hT, hH⟩)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
    case lv => exact fun le m hT => EvalLvalue.Ederef _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem)))
    case ev => exact fun le m hT => ⟨_, EvalExpr.Econst_int _ _, rfl⟩

theorem tail_cut {f : Nat → Integers.Int} {n k : Nat} (ht : Tail f 0 n) (hk : k < n) :
    Tail (upd f k Integers.Int.zero) (k + 1) n := by
  obtain ⟨_, hnz, hz, hch, hb⟩ := ht
  refine ⟨hk, fun j h1 h2 => ?_, ?_, fun j => ?_, hb⟩
  · simp [upd, show j ≠ k by omega]; exact hnz j (Nat.zero_le _) h2
  · simp [upd, show n ≠ k by omega, hz]
  · by_cases hj : j = k
    · simp [upd, hj]; decide
    · simp [upd, hj]; exact hch j

def Q11 (c : Ctx) (bp : Block) : Sep.Assn := fun e le hp =>
  ∃ y : PS × Integers.Ptrofs × (Nat → Integers.Int),
    LocalSt (E bp) ((_slash, .Vptr y.1.1 y.2.1) :: Lk c) (arr y.1.1 y.2.2 (y.1.2.2 + 1) ∗ R6 c bp y.1) e le hp

theorem s11 (ge : CGenv) (c : Ctx) (bp : Block) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (Q10 c bp ge.genv_cenv) hd10 (RR (ppPostA c) (Q11 c bp)) := by
  refine only_RR _ _ _ _ ?_
  refine triple_lift ge _ _ (fun y : PS × Nat × Integers.Ptrofs => fun e le hp => y.2.1 < y.1.2.2
    ∧ Integers.Ptrofs.unsigned y.2.2 = (y.2.1 : _root_.Int) ∧ Tail y.1.2.1 0 y.1.2.2
    ∧ LocalSt (E bp) ((_slash, .Vptr y.1.1 (inc1 ge.genv_cenv y.2.2)) :: Lk c)
        (arr y.1.1 (upd y.1.2.1 y.2.1 Integers.Int.zero) (y.1.2.2 + 1) ∗ R6 c bp y.1) e le hp) _ _ _
    (fun e le hp h => h) ?_
  intro ⟨x, k, o⟩
  refine triple_lift ge _ _ (fun (_ : k < x.2.2 ∧ Integers.Ptrofs.unsigned o = (k : _root_.Int)
      ∧ Tail x.2.1 0 x.2.2) =>
    LocalSt (E bp) ((_slash, .Vptr x.1 (inc1 ge.genv_cenv o)) :: Lk c)
      (arr x.1 (upd x.2.1 k Integers.Int.zero) (x.2.2 + 1) ∗ R6 c bp x)) _ _ _
    (fun e le hp ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩) ?_
  intro ⟨hk, ho, ht⟩
  have ho1 : Integers.Ptrofs.unsigned (inc1 ge.genv_cenv o) = ((k + 1 : Nat) : _root_.Int) :=
    incr_ofs _ o k ho (by have := ht.2.2.2.2; omega)
  refine triple_seq_fwd ge _ _ _
    (LocalSt (E bp) ((_s, .Vptr x.1 (inc1 ge.genv_cenv o)) :: (_slash, .Vptr x.1 (inc1 ge.genv_cenv o)) :: Lk c)
      (arr x.1 (upd x.2.1 k Integers.Int.zero) (x.2.2 + 1) ∗ R6 c bp x)) _ _ _ ?a ?b
  case a =>
    refine set2 ge _ _ (E bp) _ _ _s _ _ (by lfresh) ?_
    intro le m hp hT _ _
    exact EvalExpr.Etempvar _ _ _ (hT.get (by lmem))
  case b =>
    refine triple_conseq ge _ _
      (scan_loop ge _ _ (E bp) ((_slash, .Vptr x.1 (inc1 ge.genv_cenv o)) :: Lk c) (R6 c bp x) _s _t'11 _t'10
        x.1 x.2.2 (by lfresh3) (by decide) (by decide) (by decide) (x.2.2 - (k + 1)))
      ?pre ?post (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
    case pre =>
      intro e le hp hL
      refine ⟨upd x.2.1 k Integers.Int.zero, inc1 ge.genv_cenv o, by omega, ?_, ?_, hL⟩
      · rw [ho1]; congr 1; omega
      · rw [show x.2.2 - (x.2.2 - (k + 1)) = k + 1 by omega]; exact tail_cut ht hk
    case post =>
      intro e le hp ⟨fc, o', he, hT, hH⟩
      exact ⟨(x, inc1 ge.genv_cenv o, fc), he, TempsHold_mono (by lsub) hT, hH⟩

abbrev H12 (c : Ctx) (bp : Block) (x : PS) (fc : Nat → Integers.Int) (v8 : Val) : HProp :=
  cR c v8 ∗ ownStr v8 ∗ arr x.1 fc (x.2.2 + 1) ∗ cS c (.Vptr x.1 Integers.Ptrofs.zero) ∗ cD c
    ∗ Case3C.Locs [(bp, 8)]

def Q12 (c : Ctx) (bp : Block) : Sep.Assn := fun e le hp =>
  ∃ y : PS × (Nat → Integers.Int) × Val, LocalSt (E bp) (Lk c) (H12 c bp y.1 y.2.1 y.2.2) e le hp

theorem s12 (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx) (X : Ext ge) (bp : Block) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (Q11 c bp) hd11 (RR (ppPostA c) (Q12 c bp)) := by
  obtain ⟨bD, fdD, hsD, hfD, htD, hD⟩ := X.dup
  refine only_RR _ _ _ _ ?_
  refine triple_lift ge _ _ (fun y : PS × Integers.Ptrofs × (Nat → Integers.Int) =>
    LocalSt (E bp) ((_slash, .Vptr y.1.1 y.2.1) :: Lk c) (arr y.1.1 y.2.2 (y.1.2.2 + 1) ∗ R6 c bp y.1)) _ _ _
    (fun e le hp h => h) ?_
  intro ⟨x, o, fc⟩
  have hpv : IsPtr (.Vptr x.1 o) := Or.inl ⟨_, _, rfl⟩
  refine triple_seq_fwd ge _ _ _
    (fun e le hp => ∃ v8, LocalSt (E bp) ((_t'8, v8) :: (_slash, .Vptr x.1 o) :: Lk c)
      (ownStr v8 ∗ (arr x.1 fc (x.2.2 + 1) ∗ R6 c bp x)) e le hp) _ _ _ ?a ?b
  case a =>
    refine heap_eq ge _ _ _ _ _ (emp ∗ (arr x.1 fc (x.2.2 + 1) ∗ R6 c bp x)) _ _ (emp_sep_eq _).symm ?_
    refine triple_conseq ge _ _
      (call2 ge _ _ dupSpec _t'8 _ _ (E bp) _ emp _ [.Vptr x.1 o] bD fdD hD hfD htD ?hcl (by lfresh) ?cal ?args
        (fun h hh => hh))
      (fun _ _ _ x => x) (fun e le hp h => h) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
    case hcl => rfl
    case cal => exact fun _ _ _ => eval_callee_global (envP_other _ _ (by decide)) hsD rfl
    case args =>
      intro le m hT
      exact .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) (cast_ptr hpv _ _ m) .nil
  case b =>
    refine triple_lift ge _ _ (fun v8 : Val => LocalSt (E bp) ((_t'8, v8) :: (_slash, .Vptr x.1 o) :: Lk c)
      (ownStr v8 ∗ (arr x.1 fc (x.2.2 + 1) ∗ R6 c bp x))) _ _ _ (fun e le hp h => h) ?_
    intro v8
    refine lift_ptr ge _ _ (E bp) _ v8 _ _ _ ?_
    intro hv8
    have he : ownStr v8 ∗ (arr x.1 fc (x.2.2 + 1) ∗ R6 c bp x)
        = mapsto Mptr .Freeable c.reqB (Integers.Ptrofs.unsigned c.reqO) c.reqV
          ∗ (ownStr v8 ∗ arr x.1 fc (x.2.2 + 1) ∗ cS c (.Vptr x.1 Integers.Ptrofs.zero) ∗ cD c
             ∗ Case3C.Locs [(bp, 8)]) := by
      simp only [R6, cR]; ac_rfl
    rw [he]
    refine triple_conseq ge _ _
      (assign_cell ge _ _ (E bp) _ _ _ _ Mptr c.reqB c.reqO _ c.reqV v8 rfl rfl ?lv ?ev)
      (fun _ _ _ x => x) (fun e le hp ⟨he, hT, hH⟩ => ⟨(x, fc, v8), he, TempsHold_mono (by lsub) hT, hH⟩)
      (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
    case lv => exact fun le m hT => lv_reqPath hcenv (hT.get (by lmem))
    case ev => exact fun le m hT => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by lmem)), cast_ptr hv8 _ _ m⟩

abbrev H13 (c : Ctx) (bp : Block) (x : PS) (fc : Nat → Integers.Int) (q : PS) : HProp :=
  cR c (.Vptr q.1 Integers.Ptrofs.zero) ∗ strAt q.1 q.2.1 q.2.2 ∗ arr x.1 fc (x.2.2 + 1)
    ∗ cS c (.Vptr x.1 Integers.Ptrofs.zero) ∗ cD c ∗ Case3C.Locs [(bp, 8)]

def Q13 (c : Ctx) (bp : Block) : Sep.Assn := fun e le hp =>
  ∃ y : PS × (Nat → Integers.Int) × PS, LocalSt (E bp) (Lk c) (H13 c bp y.1 y.2.1 y.2.2) e le hp

theorem s13 (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx) (bp : Block) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (Q12 c bp) hd12 (RR (ppPostA c) (Q13 c bp)) := by
  refine triple_lift ge _ _ (fun y : PS × (Nat → Integers.Int) × Val =>
    LocalSt (E bp) (Lk c) (H12 c bp y.1 y.2.1 y.2.2)) _ _ _ (fun e le hp h => h) ?_
  intro ⟨x, fc, v8⟩
  have h1 : H12 c bp x fc v8 = ownStr v8 ∗ (cR c v8 ∗ arr x.1 fc (x.2.2 + 1)
      ∗ cS c (.Vptr x.1 Integers.Ptrofs.zero) ∗ cD c ∗ Case3C.Locs [(bp, 8)]) := by
    unfold H12; ac_rfl
  rw [h1]
  refine lift_ptr ge _ _ (E bp) _ v8 _ _ _ ?_
  intro hv8
  have h2 : ownStr v8 ∗ (cR c v8 ∗ arr x.1 fc (x.2.2 + 1)
      ∗ cS c (.Vptr x.1 Integers.Ptrofs.zero) ∗ cD c ∗ Case3C.Locs [(bp, 8)])
      = mapsto Mptr .Freeable c.reqB (Integers.Ptrofs.unsigned c.reqO) v8
        ∗ (ownStr v8 ∗ arr x.1 fc (x.2.2 + 1) ∗ cS c (.Vptr x.1 Integers.Ptrofs.zero) ∗ cD c
           ∗ Case3C.Locs [(bp, 8)]) := by
    unfold cR; ac_rfl
  refine triple_seq_fwd ge _ _ _ (LocalSt (E bp) ((_t'9, v8) :: Lk c) (ownStr v8 ∗ (cR c v8
    ∗ arr x.1 fc (x.2.2 + 1) ∗ cS c (.Vptr x.1 Integers.Ptrofs.zero) ∗ cD c ∗ Case3C.Locs [(bp, 8)]))) _ _ _
    ?a ?b
  case a =>
    refine set2 ge _ _ (E bp) _ _ _t'9 _ _ (by lfresh) ?_
    intro le m hp hT hH hag
    exact eval_load (lv_reqPath (b := c.reqB) (o := c.reqO) hcenv (hT.get (by lmem))) rfl
      (cell_load h2 hH hag hv8)
  case b =>
    refine lift_own ge _ _ (E bp) _ v8 _ _ _ ?n ?s
    case n =>
      intro hv; subst hv
      refine triple_if_local ge _ _ (E bp) _ _ _ true _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem)))
          notbool_null, boolVal_ofBool_tint _ m⟩) ?_
      have h3 : emp ∗ (cR c nullV ∗ arr x.1 fc (x.2.2 + 1) ∗ cS c (.Vptr x.1 Integers.Ptrofs.zero) ∗ cD c
          ∗ Case3C.Locs [(bp, 8)]) = (emp ∗ cR c nullV ∗ arr x.1 fc (x.2.2 + 1)
          ∗ cS c (.Vptr x.1 Integers.Ptrofs.zero) ∗ cD c) ∗ Case3C.Locs [(bp, 8)] := by ac_rfl
      rw [h3]
      exact ret_here ge _ _ hcenv bp _ _ _ _ _ _ _ (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)
        (fun _ => rfl) (fun hp _ => post27 c hp)
    case s =>
      intro q hv; subst hv
      have h4 : strAt q.1 q.2.1 q.2.2 ∗ (cR c (.Vptr q.1 Integers.Ptrofs.zero) ∗ arr x.1 fc (x.2.2 + 1)
          ∗ cS c (.Vptr x.1 Integers.Ptrofs.zero) ∗ cD c ∗ Case3C.Locs [(bp, 8)])
          = strAt q.1 q.2.1 q.2.2 ∗ (cR c (.Vptr q.1 Integers.Ptrofs.zero) ∗ arr x.1 fc (x.2.2 + 1)
          ∗ cS c (.Vptr x.1 Integers.Ptrofs.zero) ∗ cD c ∗ Case3C.Locs [(bp, 8)]) := rfl
      refine triple_if_local ge _ _ (E bp) _ _ _ false _ _ _ ?_ ?_
      · intro le m hp hT hH hag
        refine ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem)))
          (notbool_ptr ?_), boolVal_ofBool_tint _ m⟩
        rw [unsigned_zero]
        exact valid_str h4 hH hag (Nat.zero_le _)
      · exact triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x)
          (fun e le hp ⟨he, hT, hH⟩ => ⟨(x, fc, q), he, TempsHold_mono (by lsub) hT, by
            show H13 c bp x fc q hp
            have : H13 c bp x fc q = strAt q.1 q.2.1 q.2.2 ∗ (cR c (.Vptr q.1 Integers.Ptrofs.zero)
              ∗ arr x.1 fc (x.2.2 + 1) ∗ cS c (.Vptr x.1 Integers.Ptrofs.zero) ∗ cD c
              ∗ Case3C.Locs [(bp, 8)]) := by unfold H13; ac_rfl
            rw [this]; exact hH⟩)
          (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)

theorem s14 (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx) (bp : Block) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (Q13 c bp) tl13 (RB c) := by
  rw [tl13_ret]
  refine triple_lift ge _ _ (fun y : PS × (Nat → Integers.Int) × PS =>
    LocalSt (E bp) (Lk c) (H13 c bp y.1 y.2.1 y.2.2)) _ _ _ (fun e le hp h => h) ?_
  intro ⟨x, fc, q⟩
  have h1 : H13 c bp x fc q = (cD c ∗ cS c (.Vptr x.1 Integers.Ptrofs.zero) ∗ arr x.1 fc (x.2.2 + 1)
      ∗ cR c (.Vptr q.1 Integers.Ptrofs.zero) ∗ strAt q.1 q.2.1 q.2.2) ∗ Case3C.Locs [(bp, 8)] := by
    unfold H13; ac_rfl
  rw [h1]
  exact ret_here ge _ _ hcenv bp _ _ _ _ _ _ _ (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)
    (fun _ => rfl) (fun hp hH _ => ⟨x.1, fc, x.2.2, q.1, q.2.1, q.2.2, hH⟩)

theorem body_after (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx)
    (hup : IsPtr c.upV) (hold : IsPtr c.oldV) (X : Ext ge) (bp : Block) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path
      (LocalSt (envP bp) (Lb c) (H0 c ∗ Case3C.Locs [(bp, 8)])) f_smb_parse_url_path.fn_body
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := ppPostA c } := by
  show Triple _ _ _ _ tl0 (RB c)
  refine seg _ _ c split0 _ _ (s1 ge hcenv c hup X bp) ?_
  refine seg _ _ c split1 _ _ (s2 ge hcenv c bp) ?_
  refine seg _ _ c split2 _ _ (s3 ge hcenv c hold X bp) ?_
  refine seg _ _ c split3 _ _ (s4 ge hcenv c X bp) ?_
  refine seg _ _ c split4 _ _ (s5 ge hcenv c X bp) ?_
  refine seg _ _ c split5 _ _ (s6 ge hcenv c bp) ?_
  refine seg _ _ c split6 _ _ (s7 ge hcenv c X bp) ?_
  refine seg _ _ c split7 _ _ (s8 ge hcenv c X bp) ?_
  refine seg _ _ c split8 _ _ (s9 ge hcenv c X bp) ?_
  refine seg _ _ c split9 _ _ (s10 ge hcenv c bp) ?_
  refine seg _ _ c split10 _ _ (s11 ge c bp) ?_
  refine seg _ _ c split11 _ _ (s12 ge hcenv c X bp) ?_
  refine seg _ _ c split12 _ _ (s13 ge hcenv c bp) ?_
  exact s14 ge hcenv c bp

end Deb2026_3805C

namespace Deb2026_3805C

theorem pp_entry_wf :
    listNorepet (varNames f_smb_parse_url_path.fn_vars)
    ∧ listNorepet (varNames f_smb_parse_url_path.fn_params)
    ∧ listDisjoint (varNames f_smb_parse_url_path.fn_params) (varNames f_smb_parse_url_path.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **修正後の `smb_parse_url_path`（U1）**: 戻り値が CURLE_OK なら、`share` と `req->path` が別々に所有された文字列を指す。 -/
theorem parse_after (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx)
    (hup : IsPtr c.upV) (hold : IsPtr c.oldV) (X : Ext ge) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_smb_parse_url_path) (ppSpecA c) vs := by
  by_cases hvs : vs = [.Vptr c.dataB c.dataO, .Vptr c.smbcB c.smbcO, .Vptr c.reqB c.reqO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := pp_entry_wf
  refine satisfies_internal ge (FunctionEntry2 ge) f_smb_parse_url_path _ _
    (fun e le hp => ∃ bp, LocalSt (envP bp) (Lb c) (H0 c ∗ Case3C.Locs [(bp, 8)]) e le hp)
    (fun m hp hf hpre hd hag => ?_)
    (triple_lift ge _ _ _ _ _ _ (fun e le hp h => h) (fun bp => body_after ge hcenv c hup hold X bp))
  let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv (tptr tschar))
  have hav : AllocVariables ge.genv_cenv emptyEnv m f_smb_parse_url_path.fn_vars (envP a1.2) a1.1 :=
    .cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _)
  obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav hnv
    (by
      intro v hv
      simp only [f_smb_parse_url_path, List.mem_cons, List.mem_nil_iff, or_false] at hv
      subst hv; rw [hcenv]; decide)
    (Heap.union hp hf) hag
  have hL : Case3C.Locs [(a1.2, 8)] hl := by
    have := Case3C.locs_of_localsAt ge.genv_cenv _ _ hl hloc
    rw [hcenv] at this
    exact this
  obtain ⟨dph, dfh⟩ := Heap.disjoint_union_left.mp hdl
  refine ⟨envP a1.2,
    PTree.set _req (.Vptr c.reqB c.reqO) (PTree.set _smbc (.Vptr c.smbcB c.smbcO)
      (PTree.set _data (.Vptr c.dataB c.dataO) (createUndefTemps f_smb_parse_url_path.fn_temps))),
    a1.1, hl, FunctionEntry2.intro hnv hnp hdisj hav rfl,
    Heap.disjoint_union_left.mpr ⟨hd, Heap.disjoint_comm dfh⟩, ?_, ?_⟩
  · rw [Heap.union_assoc, Heap.union_comm (Heap.disjoint_comm dfh), ← Heap.union_assoc]
    exact hagl
  · refine ⟨a1.2, rfl, ?_, ⟨hp, hl, dph, rfl, hpre.2, hL⟩⟩
    exact TempsHold_cons (PTree.gss _ _ _)
      (TempsHold_cons ((PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _))
        (TempsHold_cons ((PTree.gso _ _ _ _ (by decide)).trans ((PTree.gso _ _ _ _ (by decide)).trans
          (PTree.gss _ _ _))) (TempsHold_nil _)))

/-- 事後条件の所有から、`share` と `req->path` のブロックが違うことを取り出す。 -/
theorem post_blocks_ne (c : Ctx) (hp : Heap) (h : ppPostA c (.Vint Integers.Int.zero) hp) :
    ∃ bs bq, bs ≠ bq ∧ ∃ fs ns fq nq, (cD c ∗ cS c (.Vptr bs Integers.Ptrofs.zero) ∗ arr bs fs (ns + 1)
      ∗ cR c (.Vptr bq Integers.Ptrofs.zero) ∗ strAt bq fq nq) hp := by
  obtain ⟨bs, fs, ns, bq, fq, nq, hH⟩ := h rfl
  refine ⟨bs, bq, ?_, fs, ns, fq, nq, hH⟩
  obtain ⟨_, h2, _, rfl, _, h3, h4, _, rfl, _, h5, h6, d5, rfl, hA, h7, h8, d7, rfl, _, hS⟩ := hH
  have hA2 := (strAt_arr hS).2
  have hd : Heap.disjoint h5 h8 := (Heap.disjoint_union_right.mp d5).2
  exact arr_ne hA hA2 hd (by omega) (by omega)

end Deb2026_3805C
