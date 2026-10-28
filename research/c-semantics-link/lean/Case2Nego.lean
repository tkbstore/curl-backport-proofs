/-
Case 2（CURL-CVE-2026-86413）: `url_match_auth_nego`（修正の前後で同じ。プロキシ無効の構成）。

証明すること（`auth_nego_eq`）: ビットの単位 `word` の `want_nego_http`（bit 1）を `want` とすると、
C の関数は H5 のモデルの `matchNego want x` と同じ判定をする。判定は、戻り値と2つの書き込みに現れる。

  reject     → FALSE。何も書かない
  candidate  → FALSE。`m->found = conn`
  forceReuse → TRUE。`m->found = conn`、`m->force_reuse = TRUE`
  accept     → TRUE。何も書かない

前提: `want_proxy_nego_http`（bit 2）は 0。プロキシ無効の構成では `url_attach_existing` の memset で 0 になり、
誰も書かない（H5 のモデルもプロキシを省いた）。
-/
import Case2Common
import Case5Config
import Case4Before
open CC CC.Sep CC.HProp
open Case2_after
open Case5C (addr call_fwd RR return_const skip_end skip_fall boolVal_ofBool_tint boolVal_ofBool_tbool
  notbool_ofBool eval_bitfield eval_field bitOf cast_ofBool_bool cast_int_bool)
open Case4C (IsPtr cast_ptr eval_deref_temp lv_field triple_pure_pre)

set_option maxRecDepth 20000

namespace Case2C

open H5.Case2 (Verdict matchNego)

/-- H5 のモデルの入力。`rawWant`・`allowed` は `matchNego` が読まないので、ここでは使わない。 -/
def negInput (c : Ctx2) (cs oe : Bool) (raw allowed : Bool) : H5.Case2.Input :=
  ⟨raw, allowed, !Integers.Int.eq c.ns Integers.Int.zero,
   c.credsV != .Vlong Integers.Int64.zero, cs, oe⟩

def retOf : Verdict → Bool
  | .forceReuse => true
  | .accept => true
  | _ => false

def foundOf (c : Ctx2) (foundV : Val) : Verdict → Val
  | .candidate => .Vptr c.connB c.connO
  | .forceReuse => .Vptr c.connB c.connO
  | _ => foundV

def wordOf (word : Integers.Int) : Verdict → Integers.Int
  | .forceReuse =>
      Integers.Int.bitfield_insert (Cop.firstBit .I32 6 1).toNat 1 word (Integers.Int.repr 1)
  | _ => word

/-- C の関数が読む値から決まる、H5 のモデルの判定。 -/
def vdOf (c : Ctx2) (word : Integers.Int) (cs oe : Bool) : Verdict :=
  matchNego (bitOf word 1) (negInput c cs oe false false)

def negoSpec (c : Ctx2) (foundV : Val) (word : Integers.Int) (cs oe : Bool) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _connectdata noattr), tptr (Ty.Tstruct _url_conn_match noattr)]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.connB c.connO, .Vptr c.mB c.mO] ∧ H2 c foundV word hp
  post := fun v hp =>
    v = Val.ofBool (retOf (vdOf c word cs oe))
    ∧ H2 c (foundOf c foundV (vdOf c word cs oe)) (wordOf word (vdOf c word cs oe)) hp
  measure := fun _ => 0

theorem nego_entry_wf :
    listNorepet (varNames f_url_match_auth_nego.fn_vars)
    ∧ listNorepet (varNames f_url_match_auth_nego.fn_params)
    ∧ listDisjoint (varNames f_url_match_auth_nego.fn_params)
        (varNames f_url_match_auth_nego.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem ne_zero_eval (ce : CompositeEnv) (n : Integers.Int) (m : Mem) :
    Cop.semBinaryOperation ce .One (.Vint n) tint (.Vint (Integers.Int.repr 0)) tint m
      = some (Val.ofBool (!Integers.Int.eq n Integers.Int.zero)) := rfl

theorem notbool_int (x : Integers.Int) (m : Mem) :
    Cop.semUnaryOperation .Onotbool (.Vint x) tint m
      = some (Val.ofBool (!(!Integers.Int.eq x Integers.Int.zero))) := rfl

/-- 抜けていく `skip`。一時変数を `l0` に絞り、事実 `φ` を持たせる。 -/
theorem fall_to (ge fe f) (l l0 : List (Ident × Val)) (Hh : HProp) (Ret : Val → HProp)
    (φ : Prop) (hsub : ∀ p ∈ l0, p ∈ l) (hφ : φ) :
    Triple ge fe f (LocalSt emptyEnv l Hh) .Sskip
      (RR Ret (fun e le hp => φ ∧ LocalSt emptyEnv l0 Hh e le hp)) :=
  triple_conseq ge fe f (triple_skip ge fe f _) (fun _ _ _ x => x)
    (fun _ _ _ ⟨he, hT, hH⟩ => ⟨hφ, he, TempsHold_mono hsub hT, hH⟩)
    (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)

theorem notbool_bit_val (w : Integers.Int) (pos : Z) (m : Mem) :
    Cop.boolVal (Val.ofBool (!(!Integers.Int.eq (Cop.bitfieldExtract .I32 .Unsigned pos 1 w)
      Integers.Int.zero))) tint m = some (!bitOf w pos) :=
  boolVal_ofBool_tint _ m

theorem boolVal_bit_val (w : Integers.Int) (pos : Z) (m : Mem) :
    Cop.boolVal (.Vint (Cop.bitfieldExtract .I32 .Unsigned pos 1 w)) tint m = some (bitOf w pos) :=
  rfl

/-- `m->found = conn;` -/
theorem assign_found (ge : CGenv) (c : Ctx2) (foundV : Val) (word : Integers.Int)
    (l : List (Ident × Val)) (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpw : permOrder c.pm .Writable = true)
    (hm : (_m, Val.Vptr c.mB c.mO) ∈ l) (hcn : (_conn, Val.Vptr c.connB c.connO) ∈ l) :
    Triple ge (FunctionEntry2 ge) f_url_match_auth_nego (LocalSt emptyEnv l (H2 c foundV word))
      (.Sassign
        (.Efield (.Ederef (.Etempvar _m (tptr (Ty.Tstruct _url_conn_match noattr)))
            (Ty.Tstruct _url_conn_match noattr)) _found (tptr (Ty.Tstruct _connectdata noattr)))
        (.Etempvar _conn (tptr (Ty.Tstruct _connectdata noattr))))
      (.only (LocalSt emptyEnv l (H2 c (.Vptr c.connB c.connO) word))) := by
  refine triple_assign ge _ _ _ _ _ _ Mptr c.pm c.mB
    (Integers.Ptrofs.add c.mO (Integers.Ptrofs.repr 0)) hpw rfl (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, h1, h2, hd, heq, hf, hr⟩ := hP
  refine ⟨foundV, .Vptr c.connB c.connO, h1, h2, hd, heq, hf,
    lv_field (eval_deref_temp (hT.get hm)) rfl (hcenv ▸ co_match) (hcenv ▸ off_found),
    ⟨_, EvalExpr.Etempvar _ _ _ (hT.get hcn), rfl⟩, fun h1' hm' hd' => ?_⟩
  exact ⟨he, hT, h1', h2, hd', rfl, hm', hr⟩

/-- `m->force_reuse = TRUE;` -/
theorem assign_force (ge : CGenv) (c : Ctx2) (word : Integers.Int)
    (l : List (Ident × Val)) (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpw : permOrder c.pm .Writable = true) (hpr : permOrder c.pm .Readable = true)
    (hm : (_m, Val.Vptr c.mB c.mO) ∈ l) :
    Triple ge (FunctionEntry2 ge) f_url_match_auth_nego
      (LocalSt emptyEnv l (H2 c (.Vptr c.connB c.connO) word))
      (.Sassign
        (.Efield (.Ederef (.Etempvar _m (tptr (Ty.Tstruct _url_conn_match noattr)))
            (Ty.Tstruct _url_conn_match noattr)) _force_reuse tint)
        (.Econst_int (Integers.Int.repr 1) tint))
      (.only (LocalSt emptyEnv l (H2 c (.Vptr c.connB c.connO) (wordOf word .forceReuse)))) := by
  refine triple_assign_bitfield ge _ _ _ _ _ _ c.pm c.mB
    (Integers.Ptrofs.add c.mO (Integers.Ptrofs.repr 40)) 6 hpw hpr rfl (by decide) (by decide)
    (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, hf, hwr, hdfr, rfl, hfc, hw, hr, hdwr, rfl, hwc, hrc⟩ := hP
  have hdfr' := Heap.disjoint_union_right.mp hdfr
  refine ⟨word, Integers.Int.repr 1, hw, Heap.union hf hr,
    Heap.disjoint_union_right.mpr ⟨Heap.disjoint_comm hdfr'.1, hdwr⟩,
    Heap.union_left_comm hdfr'.1, hwc,
    EvalLvalue.Efield_struct _ _ _ c.mB c.mO _ (coOf _url_conn_match) noattr 40
      (.Bits .I32 .Unsigned 6 1) (eval_deref_temp (hT.get hm)) rfl (hcenv ▸ co_match)
      (hcenv ▸ off_force),
    ⟨_, EvalExpr.Econst_int _ _, rfl⟩, fun h1' hm' hd' => ?_⟩
  have hd'' := Heap.disjoint_union_right.mp hd'
  refine ⟨he, hT, ?_⟩
  rw [Heap.union_left_comm hd''.1]
  exact ⟨hf, Heap.union h1' hr,
    Heap.disjoint_union_right.mpr ⟨Heap.disjoint_comm hd''.1, hdfr'.2⟩, rfl, hfc,
    h1', hr, hd''.2, rfl, hm', hrc⟩

theorem post_of (c : Ctx2) (foundV : Val) (word : Integers.Int) (cs oe : Bool) (v : Val) (hp : Heap)
    (vd : Verdict) (hvd : vdOf c word cs oe = vd) (hv : v = Val.ofBool (retOf vd))
    (hH : H2 c (foundOf c foundV vd) (wordOf word vd) hp) :
    (negoSpec c foundV word cs oe).post v hp := by
  subst hvd
  exact ⟨hv, hH⟩

end Case2C
