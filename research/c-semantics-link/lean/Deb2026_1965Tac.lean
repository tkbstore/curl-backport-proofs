/-
CVE-2026-1965: 関数の本体を経路ごとにたどる規則と戦術 `cgo`。

C1 の Case 2 は、経路ごとの証明をスクリプトで組み立てた（`case2/gen_nego.py`）。ここでは同じことを Lean の戦術でする。
文の並び `s1; s2` の途中の条件を、`s2` の「最弱の前条件」（`WP s2 R`、意味の上での定義）にする。
こうすると、`s1` の中の `if` で分かれた経路は、`s1` を抜けたあと `s2` を、その経路の仮定（`split` が作る）を持ったまま進む。
戦術は規則を当てはめるだけで、規則（下の補題）はすべて証明してある。
-/
import Deb2026_1965Common
open CC CC.Sep CC.HProp
open Case5C (addr call_fwd RR boolVal_ofBool_tint eval_field eval_bitfield bitOf
  cast_int_bool cast_ofBool_bool)
open Case4C (IsPtr cast_ptr eval_deref_temp lv_field)

set_option maxRecDepth 20000

namespace Deb2026_1965C

/-! ## 並びの規則（途中の条件を `WP` にする） -/

/-- `s` を `(e, le, hp)` から走らせると `R` で終わる。 -/
def WP (ge : CGenv) (fe : EntryRel) (f : Function) (s : Stmt) (R : Sep.ExitConds) : Sep.Assn :=
  fun e le hp => Triple ge fe f (fun e' le' hp' => e' = e ∧ le' = le ∧ hp' = hp) s R

theorem wp_triple (ge fe f) (s : Stmt) (R : Sep.ExitConds) : Triple ge fe f (WP ge fe f s R) s R := by
  intro k e le hp hf m hd hag hW
  exact hW k e le hp hf m hd hag ⟨rfl, rfl, rfl⟩

theorem wp_of {ge fe f} {Q : Sep.Assn} {s : Stmt} {R : Sep.ExitConds} (h : Triple ge fe f Q s R) :
    ∀ e le hp, Q e le hp → WP ge fe f s R e le hp := by
  intro e le hp hQ k e' le' hp' hf m hd hag ⟨he, hl, hh⟩
  subst he hl hh
  exact h k e' le' hp' hf m hd hag hQ

theorem seq_cps {ge fe f} {P : Sep.Assn} {s1 s2 : Stmt} {R : Sep.ExitConds}
    (h : Triple ge fe f P s1 { R with normal := WP ge fe f s2 R }) :
    Triple ge fe f P (.Ssequence s1 s2) R :=
  triple_seq ge fe f P _ R s1 s2 h (wp_triple ge fe f s2 R)

/-- 落ちていくだけの文の後に、続きを走らせる。 -/
theorem simple_then {ge fe f} {P Q : Sep.Assn} {a : Stmt} {R : Sep.ExitConds}
    (h1 : Triple ge fe f P a (.only Q)) (hn : ∀ e le hp, Q e le hp → R.normal e le hp) :
    Triple ge fe f P a R :=
  triple_fallthrough ge fe f P Q a R h1 hn

theorem skip_then {ge fe f} {P : Sep.Assn} {R : Sep.ExitConds}
    (hn : ∀ e le hp, P e le hp → R.normal e le hp) : Triple ge fe f P .Sskip R :=
  triple_fallthrough ge fe f P P .Sskip R (triple_skip ge fe f P) hn

/-- `return n;`（`n` は `int` の定数）。出口の条件は何でもよい。 -/
theorem ret_any {ge fe f} {l : List (Ident × Val)} {Hh : HProp} {n : Integers.Int}
    {R : Sep.ExitConds} (v' : Val)
    (hcast : ∀ m : Mem, Cop.semCast (.Vint n) tint f.fn_return m = some v')
    (hret : ∀ hp, Hh hp → R.ret v' hp)
    (hg : ∀ lbl e le hp, Sep.Assn.no e le hp → R.goto lbl e le hp := by
      intro _ _ _ _ hgg; exact hgg.elim) :
    Triple ge fe f (LocalSt emptyEnv l Hh) (.Sreturn (some (.Econst_int n tint))) R :=
  triple_conseq ge fe f
    (triple_return_local ge fe f l Hh _ R.ret (.Vint n) v'
      (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _) hcast hret)
    (fun _ _ _ x => x) (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x)
    (fun _ _ _ x => False.elim x) (fun _ _ x => x) (fun lbl e le hp x => hg lbl e le hp x)

/-! ## 式の値 -/

theorem boolVal_bit (w : Integers.Int) (pos : Z) (m : Mem) :
    Cop.boolVal (.Vint (Cop.bitfieldExtract .I32 .Unsigned pos 1 w)) tint m = some (bitOf w pos) :=
  rfl

theorem boolVal_int (r : Integers.Int) (m : Mem) :
    Cop.boolVal (.Vint r) tint m = some (!Integers.Int.eq r Integers.Int.zero) := rfl

theorem cast_bit_bool (w : Integers.Int) (pos : Z) (m : Mem) :
    Cop.semCast (.Vint (Cop.bitfieldExtract .I32 .Unsigned pos 1 w)) tint tbool m
      = some (Val.ofBool (bitOf w pos)) :=
  cast_int_bool _ m

theorem ne_zero_eval (ce' : CompositeEnv) (n : Integers.Int) (m : Mem) :
    Cop.semBinaryOperation ce' .One (.Vint n) tint (.Vint (Integers.Int.repr 0)) tint m
      = some (Val.ofBool (!Integers.Int.eq n Integers.Int.zero)) := rfl

@[simp] theorem eq_repr0 : Integers.Int.eq (Integers.Int.repr 0) Integers.Int.zero = true := by
  decide
@[simp] theorem eq_repr1 : Integers.Int.eq (Integers.Int.repr 1) Integers.Int.zero = false := by
  decide

/-! ## 一時変数を使う式の値（戦術から `apply` で使う形） -/

section
variable {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {t : Ident}

theorem ev_cast_bit {w : Integers.Int} {pos : Z}
    (hle : le.get t = some (.Vint (Cop.bitfieldExtract .I32 .Unsigned pos 1 w))) :
    EvalExpr ge e le m (.Ecast (.Etempvar t tint) tbool) (Val.ofBool (bitOf w pos)) :=
  EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ hle) (cast_bit_bool w pos m)

theorem ev_cast_ofBool {b : Bool} (hle : le.get t = some (Val.ofBool b)) :
    EvalExpr ge e le m (.Ecast (.Etempvar t tint) tbool) (Val.ofBool b) :=
  EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ hle) (Case5C.cast_ofBool_bool b m)

theorem ev_cast_int {n : Integers.Int} (hle : le.get t = some (.Vint n)) :
    EvalExpr ge e le m (.Ecast (.Etempvar t tint) tbool)
      (Val.ofBool (!Integers.Int.eq n Integers.Int.zero)) :=
  EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ hle) (Case5C.cast_int_bool n m)

theorem ev_ne0 {n : Integers.Int} (hle : le.get t = some (.Vint n)) :
    EvalExpr ge e le m
      (.Ebinop .One (.Etempvar t tint) (.Econst_int (Integers.Int.repr 0) tint) tint)
      (Val.ofBool (!Integers.Int.eq n Integers.Int.zero)) :=
  EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ hle) (EvalExpr.Econst_int _ _)
    (ne_zero_eval _ n m)

theorem ev_cast_ne0 {n : Integers.Int} (hle : le.get t = some (.Vint n)) :
    EvalExpr ge e le m
      (.Ecast (.Ebinop .One (.Etempvar t tint) (.Econst_int (Integers.Int.repr 0) tint) tint) tbool)
      (Val.ofBool (!Integers.Int.eq n Integers.Int.zero)) :=
  EvalExpr.Ecast _ _ _ _ (ev_ne0 hle) (Case5C.cast_ofBool_bool _ m)

theorem ev_cast_const (n : Integers.Int) :
    EvalExpr ge e le m (.Ecast (.Econst_int n tint) tbool)
      (Val.ofBool (!Integers.Int.eq n Integers.Int.zero)) :=
  EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) (Case5C.cast_int_bool n m)

theorem ev_temp {v : Val} {ty : Ty} (hle : le.get t = some v) :
    EvalExpr ge e le m (.Etempvar t ty) v :=
  EvalExpr.Etempvar _ _ _ hle

end

/-! ## 呼び出しと書き込み -/

theorem call_ts {ge : CGenv} {f : Function} {cmp : Val → Val → Integers.Int} (X : TsExt ge cmp)
    {l : List (Ident × Val)} {Hh : HProp} {id t1 t2 : Ident} {a b : Val}
    (ha : (t1, a) ∈ l) (hb : (t2, b) ∈ l) (pa : IsPtr a) (pb : IsPtr b) :
    Triple ge (FunctionEntry2 ge) f (LocalSt emptyEnv l Hh)
      (.Scall (some id)
        (.Evar (identOfString "Curl_timestrcmp")
          (.Tfunction [tptr tschar, tptr tschar] tint cc_default))
        [.Etempvar t1 (tptr tschar), .Etempvar t2 (tptr tschar)])
      (.only (LocalSt emptyEnv (setLocal l id (.Vint (cmp a b))) Hh)) :=
  call_fwd ge _ _ (tsSpec a b (cmp a b)) id _ _ emptyEnv l emp Hh emp Hh Hh [a, b]
    (.Vint (cmp a b)) X.b X.fd (X.hsat a b) X.hf X.hty rfl
    (fun _ _ _ => eval_callee_global rfl X.hs rfl)
    (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar t1 _ a (hT.get ha))
      (cast_ptr pa _ _ m)
      (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar t2 _ b (hT.get hb))
        (cast_ptr pb _ _ m) EvalExprlist.nil))
    (fun _ he => ⟨rfl, he⟩) (fun _ _ hp => hp) (emp_sep_eq _).symm (emp_sep_eq _)

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
    (Integers.Ptrofs.add c.mO (Integers.Ptrofs.repr 16)) 4 hpw hpr rfl (by decide) (by decide)
    (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, hf, hwr, hdfr, rfl, hfc, hw, hr, hdwr, rfl, hwc, hrc⟩ := hP
  have hdfr' := Heap.disjoint_union_right.mp hdfr
  refine ⟨w, Integers.Int.repr 1, hw, Heap.union hf hr,
    Heap.disjoint_union_right.mpr ⟨Heap.disjoint_comm hdfr'.1, hdwr⟩,
    Heap.union_left_comm hdfr'.1, hwc,
    EvalLvalue.Efield_struct _ _ _ c.mB c.mO _ coMatch noattr 16
      (.Bits .I32 .Unsigned 4 1) (eval_deref_temp (hT.get hm)) rfl L.co_match
      L.off_force,
    ⟨_, EvalExpr.Econst_int _ _, rfl⟩, fun h1' hm' hd' => ?_⟩
  have hd'' := Heap.disjoint_union_right.mp hd'
  refine ⟨he, hT, ?_⟩
  rw [Heap.union_left_comm hd''.1]
  exact ⟨hf, Heap.union h1' hr,
    Heap.disjoint_union_right.mpr ⟨Heap.disjoint_comm hd''.1, hdfr'.2⟩, rfl, hfc,
    h1', hr, hd''.2, rfl, hm', hrc⟩

/-! ## 戦術

衛生（hygiene）を切って、証明の文脈にある名前（`L`・`hpr`・`hpw`・`hptr`・`X`、
評価の段の `hT`・`hH`・`hag`）を直接使う。 -/

/-- 一時変数の値を読む（`(id, v) ∈ l`。`v` は未定でもよい）。 -/
macro "tget" : tactic => `(tactic| focus
  repeat (first
    | exact CC.Sep.mem_setLocal_head _ _ _
    | (apply CC.Sep.mem_setLocal_of_mem'; rotate_left; with_unfolding_all decide)
    | exact List.mem_cons_self
    | apply List.mem_cons_of_mem
    | fail "tget")
  done)

set_option hygiene false in
/-- 式の値（`EvalExpr` のゴール）。入れ子の `by` は使わない（失敗が `first` に届かないため）。 -/
macro "cev" : tactic => `(tactic| first
  | (refine Case5C.eval_bitfield (hT.get ?_) L.co_match L.off_wn (by decide) (by decide)
        (H_loads hpr hptr hH hag).word
     tget)
  | (refine Case5C.eval_bitfield (hT.get ?_) L.co_match L.off_wpn (by decide) (by decide)
        (H_loads hpr hptr hH hag).word
     tget)
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
  | (refine Case5C.eval_field (hT.get ?_) L.co_conn L.off_hns rfl (H_loads hpr hptr hH hag).hns
     tget)
  | (refine Case5C.eval_field (hT.get ?_) L.co_conn L.off_pns rfl (H_loads hpr hptr hH hag).pns
     tget)
  | exact EvalExpr.Econst_int _ _
  | (apply ev_cast_bit; apply hT.get; tget)
  | (apply ev_cast_ofBool; apply hT.get; tget)
  | (apply ev_cast_int; apply hT.get; tget)
  | (apply ev_cast_ne0; apply hT.get; tget)
  | exact ev_cast_const _
  | (apply ev_ne0; apply hT.get; tget)
  | (apply ev_temp; apply hT.get; tget)
  | fail "cev")

set_option hygiene false in
/-- 条件の真偽（`Cop.boolVal` のゴール）。 -/
macro "cbv" : tactic => `(tactic| first
  | exact boolVal_bit _ _ _
  | exact Case5C.boolVal_ofBool_tint _ _
  | exact boolVal_int _ _
  | fail "cbv")

set_option hygiene false in
/-- 落ちていくだけの文（代入・呼び出し・書き込み）。後条件は `.only _`。 -/
macro "csimple" : tactic => `(tactic| first
  | (apply triple_set_local_fwd
     intro le m hp hT hH hag
     cev)
  | (apply call_ts X
     · tget
     · tget
     · assumption
     · assumption)
  | (apply assign_found L _ _ _ _ hpw
     · tget
     · tget)
  | (apply assign_force L _ _ _ _ hpw hpr
     tget)
  | fail "csimple")

set_option hygiene false in
/-- 経路の仮定から判定を示す。閉じなければ失敗する。 -/
macro "cvd" : tactic => `(tactic| focus (simp_all [vdOf, verdict, gateU1, gateU0]; done))

set_option hygiene false in
/-- `return n;`。判定を4通り試し、経路の仮定から `vdOf … = vd` を示せたものを使う。 -/
macro "cret" : tactic => `(tactic| first
  | (refine ret_any (Val.ofBool false) ?_ (fun hp hH => ?_)
     · intro _; with_unfolding_all rfl
     refine post_of .reject ?_ rfl hH
     cvd)
  | (refine ret_any (Val.ofBool false) ?_ (fun hp hH => ?_)
     · intro _; with_unfolding_all rfl
     refine post_of .candidate ?_ rfl hH
     cvd)
  | (refine ret_any (Val.ofBool true) ?_ (fun hp hH => ?_)
     · intro _; with_unfolding_all rfl
     refine post_of .forceReuse ?_ rfl hH
     cvd)
  | (refine ret_any (Val.ofBool true) ?_ (fun hp hH => ?_)
     · intro _; with_unfolding_all rfl
     refine post_of .accept ?_ rfl hH
     cvd)
  | fail "cret")

set_option hygiene false in
/-- 1段だけ進める（文の形で規則が1つに決まる。深い後戻りはしない）。 -/
macro "cstep" : tactic => `(tactic| focus first
  | (apply triple_seq_fwd
     csimple)
  | apply seq_cps
  | (apply triple_if_local
     · intro le m hp hT hH hag
       apply Exists.intro
       constructor
       · cev
       · cbv
     split
     all_goals try (focus (simp_all only [eq_repr0, eq_repr1, Bool.not_true, Bool.not_false,
       Bool.false_eq_true, not_true_eq_false, not_false_eq_true]; done)))
  | (apply simple_then
     csimple
     apply wp_of)
  | refine skip_then (wp_of ?_)
  | cret
  | fail "cstep")

/-- 関数の本体を、すべての経路について最後まで進める。 -/
macro "cgo" : tactic => `(tactic| ((repeat cstep); done))

end Deb2026_1965C
