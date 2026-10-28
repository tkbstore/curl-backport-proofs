/-
CVE-2026-4873: 経路をたどる戦術（`Deb2026_1965Tac.lean` の規則を使う。式と呼び出しの候補だけをこの関数に合わせた）。
-/
import Deb2026_4873Common
open CC CC.Sep CC.HProp

set_option maxRecDepth 20000

namespace Deb2026_4873C

set_option hygiene false in
/-- 式の値（`EvalExpr` のゴール）。 -/
macro "e4ev" : tactic => `(tactic| first
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
  | (refine Case5C.eval_bitfield (hT.get ?_) L.co_match L.off_req (by decide) (by decide)
        (H_loads hpr hH hag).word
     tget)
  | exact EvalExpr.Econst_int _ _
  | (apply Case5C.eval_flag0; apply hT.get; tget)
  | (apply Case5C.eval_notflag15; apply hT.get; tget)
  | (apply ev_notbool; apply hT.get; tget)
  | (apply Case5C.eval_ne_cast
     · apply hT.get; tget
     · apply hT.get; tget)
  | (apply ev_ne_long
     · apply hT.get; tget
     · apply hT.get; tget)
  | (apply Deb2026_1965C.ev_temp; apply hT.get; tget)
  | fail "e4ev")

set_option hygiene false in
macro "e4bv" : tactic => `(tactic| first
  | exact Deb2026_1965C.boolVal_bit _ _ _
  | exact Case5C.boolVal_flag0 _ _
  | exact Case5C.boolVal_ofBool_tint _ _
  | exact Case5C.boolVal_ofBool_tbool _ _
  | exact Deb2026_1965C.boolVal_int _ _
  | fail "e4bv")

set_option hygiene false in
macro "e4simple" : tactic => `(tactic| first
  | (apply triple_set_local_fwd
     intro le m hp hT hH hag
     e4ev)
  | (apply call_ssl XS; tget)
  | (apply call_gpf XG; tget)
  | fail "e4simple")

set_option hygiene false in
macro "e4vd" : tactic => `(tactic| focus (simp_all [retOf, ret]; done))

set_option hygiene false in
macro "e4ret" : tactic => `(tactic| first
  | (refine Deb2026_1965C.ret_any (Val.ofBool false) ?_ (fun hp hH => ?_)
     · intro _; with_unfolding_all rfl
     refine post_of false ?_ rfl hH
     e4vd)
  | (refine Deb2026_1965C.ret_any (Val.ofBool true) ?_ (fun hp hH => ?_)
     · intro _; with_unfolding_all rfl
     refine post_of true ?_ rfl hH
     e4vd)
  | fail "e4ret")

set_option hygiene false in
macro "e4step" : tactic => `(tactic| focus first
  | (apply triple_seq_fwd
     e4simple)
  | apply Deb2026_1965C.seq_cps
  | (apply triple_if_local
     · intro le m hp hT hH hag
       apply Exists.intro
       constructor
       · e4ev
       · e4bv
     split
     all_goals try (focus (simp_all only [Deb2026_1965C.eq_repr0, Deb2026_1965C.eq_repr1,
       Bool.not_true, Bool.not_false, Bool.false_eq_true, not_true_eq_false, not_false_eq_true]; done)))
  | (apply Deb2026_1965C.simple_then
     e4simple
     apply Deb2026_1965C.wp_of)
  | refine Deb2026_1965C.skip_then (Deb2026_1965C.wp_of ?_)
  | e4ret
  | fail "e4step")

macro "e4go" : tactic => `(tactic| ((repeat e4step); done))

/-! ## `get_protocol_family` の本体（`DEBUGASSERT` 2つと `return s->family;`） -/

theorem triple_nop_loop (ge fe f) (P : Sep.Assn) (R : Sep.ExitConds) :
    Triple ge fe f P (.Sloop .Sskip .Sbreak) { R with normal := P } :=
  triple_weaken_only ge fe f (Case5C.triple_nop_loop ge fe f P)

end Deb2026_4873C
