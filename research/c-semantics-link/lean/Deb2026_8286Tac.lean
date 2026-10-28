/-
CVE-2026-8286: 経路をたどる戦術（CVE-2026-4873 の `Deb2026_4873Tac.lean` を写した。`Deb2026_1965Tac.lean` の規則を使う。式と呼び出しの候補だけをこの関数に合わせた）。
-/
import Deb2026_8286Common
open CC CC.Sep CC.HProp

set_option maxRecDepth 20000

namespace Deb2026_8286C

set_option hygiene false in
/-- 式の値（`EvalExpr` のゴール）。 -/
macro "p8ev" : tactic => `(tactic| first
  | (refine Case5C.eval_field (hT.get ?_) L.co_match L.off_needle rfl (H_loads hpr hH hag).needle
     tget)
  | (refine Case5C.eval_field (hT.get ?_) L.co_conn L.off_sch rfl (H_loads hpr hH hag).nsch
     tget)
  | (refine Case5C.eval_field (hT.get ?_) L.co_conn L.off_sch rfl (H_loads hpr hH hag).csch
     tget)
  | (refine Case5C.eval_field (hT.get ?_) L.co_sch L.off_flags rfl (H_loads hpr hH hag).flags
     tget)
  | (refine Case5C.eval_field (hT.get ?_) L.co_sch L.off_protocol rfl (H_loads hpr hH hag).proto
     tget)
  | (refine Case5C.eval_field (hT.get ?_) L.co_sch L.off_family rfl (H_loads hpr hH hag).fam
     tget)
  | (refine Case5C.eval_field (hT.get ?_) L.co_match L.off_data rfl (H_loads hpr hH hag).data
     tget)
  | (refine Case5C.eval_bitfield (hT.get ?_) L.co_match L.off_may (by decide) (by decide)
        (H_loads hpr hH hag).word
     tget)
  | (refine Case5C.eval_bitfield (hT.get ?_) L.co_match L.off_require (by decide) (by decide)
        (H_loads hpr hH hag).word
     tget)
  | (refine Case5C.eval_bitfield (hT.get ?_) L.co_match L.off_req (by decide) (by decide)
        (H_loads hpr hH hag).word
     tget)
  | exact EvalExpr.Econst_int _ _
  | (apply Case5C.eval_flag0; apply hT.get; tget)
  | (apply Case5C.eval_notflag15; apply hT.get; tget)
  | (apply ev_notbool; apply hT.get; tget)
  | (apply ev_cast_notbool; apply hT.get; tget)
  | (apply Deb2026_1965C.ev_cast_bit; apply hT.get; tget)
  | (apply Deb2026_1965C.ev_cast_ofBool; apply hT.get; tget)
  | (apply Case5C.eval_ne_cast
     · apply hT.get; tget
     · apply hT.get; tget)
  | (apply ev_ne_long
     · apply hT.get; tget
     · apply hT.get; tget)
  | (apply Deb2026_1965C.ev_temp; apply hT.get; tget)
  | fail "p8ev")

set_option hygiene false in
macro "p8bv" : tactic => `(tactic| first
  | exact Deb2026_1965C.boolVal_bit _ _ _
  | exact Case5C.boolVal_flag0 _ _
  | exact Case5C.boolVal_ofBool_tint _ _
  | exact Case5C.boolVal_ofBool_tbool _ _
  | exact Deb2026_1965C.boolVal_int _ _
  | fail "p8bv")

set_option hygiene false in
macro "p8simple" : tactic => `(tactic| first
  | (apply triple_set_local_fwd
     intro le m hp hT hH hag
     p8ev)
  | (apply call_ssl XS; tget)
  | (apply call_gpf XG; tget)
  | (apply call_cfg XC
     · tget
     · tget)
  | exact Case5C.triple_nop_loop _ _ _ _
  | fail "p8simple")

set_option hygiene false in
macro "p8vd" : tactic => `(tactic| focus (simp_all [useRet, cfgRet, ret]; done))

set_option hygiene false in
macro "p8ret" : tactic => `(tactic| first
  | (refine Deb2026_1965C.ret_any (Val.ofBool false) ?_ (fun hp hH => ?_)
     · intro _; with_unfolding_all rfl
     refine post_use false ?_ rfl hH
     p8vd)
  | (refine Deb2026_1965C.ret_any (Val.ofBool true) ?_ (fun hp hH => ?_)
     · intro _; with_unfolding_all rfl
     refine post_use true ?_ rfl hH
     p8vd)
  | (refine Deb2026_1965C.ret_any (Val.ofBool false) ?_ (fun hp hH => ?_)
     · intro _; with_unfolding_all rfl
     refine post_cfg false ?_ rfl hH
     p8vd)
  | (refine Deb2026_1965C.ret_any (Val.ofBool true) ?_ (fun hp hH => ?_)
     · intro _; with_unfolding_all rfl
     refine post_cfg true ?_ rfl hH
     p8vd)
  | fail "p8ret")

set_option hygiene false in
macro "p8step" : tactic => `(tactic| focus first
  | (apply triple_seq_fwd
     p8simple)
  | apply Deb2026_1965C.seq_cps
  | (apply triple_if_local
     · intro le m hp hT hH hag
       apply Exists.intro
       constructor
       · p8ev
       · p8bv
     split
     all_goals try (focus (simp_all only [Deb2026_1965C.eq_repr0, Deb2026_1965C.eq_repr1,
       Bool.not_true, Bool.not_false, Bool.false_eq_true, not_true_eq_false, not_false_eq_true]; done)))
  | (apply Deb2026_1965C.simple_then
     p8simple
     apply Deb2026_1965C.wp_of)
  | refine Deb2026_1965C.skip_then (Deb2026_1965C.wp_of ?_)
  | p8ret
  | fail "p8step")

macro "p8go" : tactic => `(tactic| ((repeat p8step); done))

end Deb2026_8286C
