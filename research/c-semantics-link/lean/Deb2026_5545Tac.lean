/-
CVE-2026-5545: 経路をたどる戦術（`Deb2026_1965Tac.lean` の規則と `tget` を使い、式の候補と書き込みだけをこの関数に合わせた）。
-/
import Deb2026_5545Common
open CC CC.Sep CC.HProp
open Case5C (addr call_fwd RR bitOf)
open Case4C (IsPtr cast_ptr eval_deref_temp lv_field)

set_option maxRecDepth 20000

namespace Deb2026_5545C

/-- `m->found = conn;` -/
theorem assign_found {ge : CGenv} {f : Function} (L : Layout ge.genv_cenv) (c : Ctx)
    (fv : Val) (w : Integers.Int) (l : List (Ident × Val))
    (hpw : permOrder c.pm .Writable = true)
    (hm : (identOfString "m", Val.Vptr c.mB c.mO) ∈ l)
    (hcn : (identOfString "conn", Val.Vptr c.connB c.connO) ∈ l) :
    Triple ge (FunctionEntry2 ge) f (LocalSt emptyEnv l (H c fv w))
      (.Sassign
        (.Efield (.Ederef (.Etempvar (identOfString "m")
            (tptr (Ty.Tstruct (identOfString "url_conn_match") noattr)))
            (Ty.Tstruct (identOfString "url_conn_match") noattr)) (identOfString "found")
            (tptr (Ty.Tstruct (identOfString "connectdata") noattr)))
        (.Etempvar (identOfString "conn") (tptr (Ty.Tstruct (identOfString "connectdata") noattr))))
      (.only (LocalSt emptyEnv l (H c (.Vptr c.connB c.connO) w))) := by
  refine triple_assign ge _ _ _ _ _ _ Mptr c.pm c.mB
    (Integers.Ptrofs.add c.mO (Integers.Ptrofs.repr 0)) hpw rfl (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, h1, h2, hd, heq, hf, hr⟩ := hP
  refine ⟨fv, .Vptr c.connB c.connO, h1, h2, hd, heq, hf,
    lv_field (eval_deref_temp (hT.get hm)) rfl L.co_match L.off_found,
    ⟨_, EvalExpr.Etempvar _ _ _ (hT.get hcn), rfl⟩, fun h1' hm' hd' => ?_⟩
  exact ⟨he, hT, h1', h2, hd', rfl, hm', hr⟩

/-- `m->force_reuse = TRUE;` -/
theorem assign_force {ge : CGenv} {f : Function} (L : Layout ge.genv_cenv) (c : Ctx)
    (fv : Val) (w : Integers.Int) (l : List (Ident × Val))
    (hpw : permOrder c.pm .Writable = true) (hpr : permOrder c.pm .Readable = true)
    (hm : (identOfString "m", Val.Vptr c.mB c.mO) ∈ l) :
    Triple ge (FunctionEntry2 ge) f (LocalSt emptyEnv l (H c fv w))
      (.Sassign
        (.Efield (.Ederef (.Etempvar (identOfString "m")
            (tptr (Ty.Tstruct (identOfString "url_conn_match") noattr)))
            (Ty.Tstruct (identOfString "url_conn_match") noattr)) (identOfString "force_reuse") tint)
        (.Econst_int (Integers.Int.repr 1) tint))
      (.only (LocalSt emptyEnv l (H c fv (forceWord w)))) := by
  refine Case2C.triple_assign_bitfield ge _ _ _ _ _ _ c.pm c.mB
    (Integers.Ptrofs.add c.mO (Integers.Ptrofs.repr 16)) 2 hpw hpr rfl (by decide) (by decide)
    (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, hf, hwr, hdfr, rfl, hfc, hw, hr, hdwr, rfl, hwc, hrc⟩ := hP
  have hdfr' := Heap.disjoint_union_right.mp hdfr
  refine ⟨w, Integers.Int.repr 1, hw, Heap.union hf hr,
    Heap.disjoint_union_right.mpr ⟨Heap.disjoint_comm hdfr'.1, hdwr⟩,
    Heap.union_left_comm hdfr'.1, hwc,
    EvalLvalue.Efield_struct _ _ _ c.mB c.mO _ coMatch noattr 16
      (.Bits .I32 .Unsigned 2 1) (eval_deref_temp (hT.get hm)) rfl L.co_match
      L.off_force,
    ⟨_, EvalExpr.Econst_int _ _, rfl⟩, fun h1' hm' hd' => ?_⟩
  have hd'' := Heap.disjoint_union_right.mp hd'
  refine ⟨he, hT, ?_⟩
  rw [Heap.union_left_comm hd''.1]
  exact ⟨hf, Heap.union h1' hr,
    Heap.disjoint_union_right.mpr ⟨Heap.disjoint_comm hd''.1, hdfr'.2⟩, rfl, hfc,
    h1', hr, hd''.2, rfl, hm', hrc⟩

/-! ## `t == 0`（`NTLMSTATE_NONE`・`GSS_AUTHNONE` との比較） -/

theorem eq_zero_eval (ce' : CompositeEnv) (n : Integers.Int) (m : Mem) :
    Cop.semBinaryOperation ce' .Oeq (.Vint n) tint (.Vint (Integers.Int.repr 0)) tint m
      = some (Val.ofBool (Integers.Int.eq n Integers.Int.zero)) := rfl

section
variable {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {t : Ident}

theorem ev_eq0 {n : Integers.Int} (hle : le.get t = some (.Vint n)) :
    EvalExpr ge e le m
      (.Ebinop .Oeq (.Etempvar t tint) (.Econst_int (Integers.Int.repr 0) tint) tint)
      (Val.ofBool (Integers.Int.eq n Integers.Int.zero)) :=
  EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hle) (EvalExpr.Econst_int _ _)
    (eq_zero_eval _ n m)

theorem ev_cast_eq0 {n : Integers.Int} (hle : le.get t = some (.Vint n)) :
    EvalExpr ge e le m
      (.Ecast (.Ebinop .Oeq (.Etempvar t tint) (.Econst_int (Integers.Int.repr 0) tint) tint) tbool)
      (Val.ofBool (Integers.Int.eq n Integers.Int.zero)) :=
  EvalExpr.Ecast _ _ _ _ (ev_eq0 hle) (Case5C.cast_ofBool_bool _ m)

end

/-! ## 戦術

衛生（hygiene）を切って、証明の文脈にある名前（`L`・`hpr`・`hpw`・`hptr`・`X`、
評価の段の `hT`・`hH`・`hag`）を直接使う。 -/

set_option hygiene false in
/-- 式の値（`EvalExpr` のゴール）。入れ子の `by` は使わない（失敗が `first` に届かないため）。 -/
macro "n5ev" : tactic => `(tactic| first
  | (refine Case5C.eval_bitfield (hT.get ?_) L.co_match L.off_wt (by decide) (by decide)
        (H_loads hpr hptr hH hag).word
     tget)
  | (refine Case5C.eval_bitfield (hT.get ?_) L.co_match L.off_wpt (by decide) (by decide)
        (H_loads hpr hptr hH hag).word
     tget)
  | (refine Case5C.eval_field (hT.get ?_) L.co_match L.off_needle rfl (H_loads hpr hptr hH hag).needle
     tget)
  | (refine Case5C.eval_field (hT.get ?_) L.co_conn L.off_user rfl (H_loads hpr hptr hH hag).nu
     tget)
  | (refine Case5C.eval_field (hT.get ?_) L.co_conn L.off_user rfl (H_loads hpr hptr hH hag).cu
     tget)
  | (refine Case5C.eval_field (hT.get ?_) L.co_conn L.off_passwd rfl (H_loads hpr hptr hH hag).np
     tget)
  | (refine Case5C.eval_field (hT.get ?_) L.co_conn L.off_passwd rfl (H_loads hpr hptr hH hag).cp
     tget)
  | (refine Case5C.eval_field (hT.get ?_) L.co_conn L.off_hnt rfl (H_loads hpr hptr hH hag).hnt
     tget)
  | (refine Case5C.eval_field (hT.get ?_) L.co_conn L.off_pnt rfl (H_loads hpr hptr hH hag).pnt
     tget)
  | (refine Case5C.eval_field (hT.get ?_) L.co_conn L.off_hns rfl (H_loads hpr hptr hH hag).hns
     tget)
  | exact EvalExpr.Econst_int _ _
  | (apply Deb2026_1965C.ev_cast_bit; apply hT.get; tget)
  | (apply Deb2026_1965C.ev_cast_ofBool; apply hT.get; tget)
  | (apply Deb2026_1965C.ev_cast_int; apply hT.get; tget)
  | (apply Deb2026_1965C.ev_cast_ne0; apply hT.get; tget)
  | exact Deb2026_1965C.ev_cast_const _
  | (apply Deb2026_1965C.ev_ne0; apply hT.get; tget)
  | (apply ev_cast_eq0; apply hT.get; tget)
  | (apply ev_eq0; apply hT.get; tget)
  | (apply Deb2026_1965C.ev_temp; apply hT.get; tget)
  | fail "n5ev")

set_option hygiene false in
/-- 条件の真偽（`Cop.boolVal` のゴール）。 -/
macro "n5bv" : tactic => `(tactic| first
  | exact Deb2026_1965C.boolVal_bit _ _ _
  | exact Case5C.boolVal_ofBool_tint _ _
  | exact Deb2026_1965C.boolVal_int _ _
  | fail "n5bv")

set_option hygiene false in
/-- 落ちていくだけの文（代入・呼び出し・書き込み）。後条件は `.only _`。 -/
macro "n5simple" : tactic => `(tactic| first
  | (apply triple_set_local_fwd
     intro le m hp hT hH hag
     n5ev)
  | (apply Deb2026_1965C.call_ts X
     · tget
     · tget
     · assumption
     · assumption)
  | (apply assign_found L _ _ _ _ hpw
     · tget
     · tget)
  | (apply assign_force L _ _ _ _ hpw hpr
     tget)
  | fail "n5simple")

set_option hygiene false in
/-- 経路の仮定から判定を示す。閉じなければ失敗する。 -/
macro "n5vd" : tactic => `(tactic| focus (simp_all [vdOf, verdict]; done))

set_option hygiene false in
/-- `return n;`。判定を4通り試し、経路の仮定から `vdOf … = vd` を示せたものを使う。 -/
macro "n5ret" : tactic => `(tactic| first
  | (refine Deb2026_1965C.ret_any (Val.ofBool false) ?_ (fun hp hH => ?_)
     · intro _; with_unfolding_all rfl
     refine post_of .reject ?_ rfl hH
     n5vd)
  | (refine Deb2026_1965C.ret_any (Val.ofBool false) ?_ (fun hp hH => ?_)
     · intro _; with_unfolding_all rfl
     refine post_of .candidate ?_ rfl hH
     n5vd)
  | (refine Deb2026_1965C.ret_any (Val.ofBool true) ?_ (fun hp hH => ?_)
     · intro _; with_unfolding_all rfl
     refine post_of .forceReuse ?_ rfl hH
     n5vd)
  | (refine Deb2026_1965C.ret_any (Val.ofBool true) ?_ (fun hp hH => ?_)
     · intro _; with_unfolding_all rfl
     refine post_of .accept ?_ rfl hH
     n5vd)
  | fail "n5ret")

set_option hygiene false in
/-- 1段だけ進める（文の形で規則が1つに決まる。深い後戻りはしない）。 -/
macro "n5step" : tactic => `(tactic| focus first
  | (apply triple_seq_fwd
     n5simple)
  | apply Deb2026_1965C.seq_cps
  | (apply triple_if_local
     · intro le m hp hT hH hag
       apply Exists.intro
       constructor
       · n5ev
       · n5bv
     split
     all_goals try (focus (simp_all only [Deb2026_1965C.eq_repr0, Deb2026_1965C.eq_repr1, Bool.not_true, Bool.not_false,
       Bool.false_eq_true, not_true_eq_false, not_false_eq_true]; done)))
  | (apply Deb2026_1965C.simple_then
     n5simple
     apply Deb2026_1965C.wp_of)
  | refine Deb2026_1965C.skip_then (Deb2026_1965C.wp_of ?_)
  | n5ret
  | fail "n5step")

/-- 関数の本体を、すべての経路について最後まで進める。 -/
macro "n5go" : tactic => `(tactic| ((repeat n5step); done))

end Deb2026_5545C
