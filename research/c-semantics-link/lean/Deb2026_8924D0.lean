/-
CVE-2026-8924: curl 8.14.1（D0、パッチを当てる前）の `is_public_suffix`。

証明すること（`ps_before`、P0）: `co->domain` の長さ `cl`（256 未満）の最後の文字が `.` のとき、`Curl_strntolower` が小文字にして写す
（`lcookie` の `cl-1` 番目が `.` になる）なら、`psl_is_cookie_domain_acceptable` を `lcookie` の `cl-1` 番目が `.` のまま呼ぶ
（その仕様の事前条件にこれを入れる）。libpsl が受け入れる（`acc` が 0 でない）と、戻り値は CERR_OK（Cookie を捨てない）。
-/
import GenDeb2026_8924D0
import Deb2026_8924D1
open CC CC.Sep CC.HProp
open Deb2026_8924_d0
open Deb2026_8924
open Deb2025_14524 (specK callK_none callS_some weaken pre_conv cell_valid boolVal_ptr cast_bool_ptr
  boolVal_ofBool_int)
open Case5C (addr RR return_const eval_field triple_nop_loop)
open Case4debC (lv_field eval_deref_temp)
open Case3C (CellD cellH Cells cell_load3 Locs)

set_option maxRecDepth 20000

namespace Deb2026_8924D

/-- `lcookie` の `cl-1` 番目が `.`（46）の形。 -/
def WQ (c : Ctx) (b1 b2 : Block) : HProp :=
  Hc c ∗ (anyBytes .Freeable b1 0 256 ∗ (Arr3 b2 (c.cl - 1) (.Vint (Integers.Int.repr 46)) ∗ emp))

def psSpecB (c : Ctx) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _Cookie noattr), tptr tschar]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = argsP c ∧ Hc c hp
  post := fun v hp => v = .Vint (Integers.Int.repr 0) ∧ Hc c hp
  measure := fun _ => 0

structure ExtP0 (ge : CGenv) (c : Ctx) (acc : Integers.Int) where
  fdS : FunDef
  sl : Callee ge _strlen fdS
  tS : typeOfFundef fdS = .Tfunction [tptr tschar] tulong cc_default
  sS1 : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdS (strlenSpec (.Vptr c.mB c.mO) c.dl (W0 c b1 b2)) vs
  sS2 : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdS (strlenSpec (.Vptr c.kB c.kO) c.cl (W0 c b1 b2)) vs
  fdI : FunDef
  ip : Callee ge _Curl_host_is_ipnum fdI
  tI : typeOfFundef fdI = .Tfunction [tptr tschar] tbool cc_default
  sI : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdI
    (specK [tptr tschar] tbool cc_default (W0 c b1 b2) (W0 c b1 b2) (some (Val.ofBool false))) vs
  fdU : FunDef
  pu : Callee ge _Curl_psl_use fdU
  tU : typeOfFundef fdU = .Tfunction [tptr (Ty.Tstruct _Curl_easy noattr)]
    (tptr (Ty.Tstruct _psl_ctx_st noattr)) cc_default
  sU : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdU
    (specK [tptr (Ty.Tstruct _Curl_easy noattr)] (tptr (Ty.Tstruct _psl_ctx_st noattr)) cc_default
      (W0 c b1 b2) (W0 c b1 b2) (some (.Vptr c.pB c.pO))) vs
  fdL : FunDef
  lw : Callee ge _Curl_strntolower fdL
  tL : typeOfFundef fdL = .Tfunction sltTy tvoid cc_default
  sL1 : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdL
    (specK sltTy tvoid cc_default (W0 c b1 b2) (W0 c b1 b2) none) vs
  /-- 小文字にして写す（`co->domain` の `cl-1` 番目の `.` が `lcookie` の `cl-1` 番目に入る）。 -/
  sL2 : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdL
    (specK sltTy tvoid cc_default (W0 c b1 b2) (WQ c b1 b2) none) vs
  fdP : FunDef
  ps : Callee ge _psl_is_cookie_domain_acceptable fdP
  tP : typeOfFundef fdP = .Tfunction [tptr (Ty.Tstruct _psl_ctx_st noattr), tptr tschar, tptr tschar]
    tint cc_default
  sP : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdP (pslSpec (WQ c b1 b2) acc) vs
  fdR : FunDef
  pr : Callee ge _Curl_psl_release fdR
  tR : typeOfFundef fdR = .Tfunction [tptr (Ty.Tstruct _Curl_easy noattr)] tvoid cc_default
  sR : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdR
    (specK [tptr (Ty.Tstruct _Curl_easy noattr)] tvoid cc_default (WQ c b1 b2) (WQ c b1 b2) none) vs

def envP0 (b1 b2 : Block) : Env :=
  (emptyEnv.set _lcase (b1, tarray tschar 256)).set _lcookie (b2, tarray tschar 256)

abbrev lP0 (c : Ctx) : List (Ident × Val) :=
  [(_domain, .Vptr c.mB c.mO), (_co, .Vptr c.coB c.coO), (_data, .Vptr c.dB c.dO)]

def PbodyP0 (c : Ctx) : Sep.Assn := fun e le hp =>
  ∃ bs : Block × Block, bs.1 ≠ bs.2 ∧
    LocalSt (envP0 bs.1 bs.2) (lP0 c) (W0 c bs.1 bs.2) e le hp

theorem blocks_envP0 (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (b1 b2 : Block) :
    blocksOfEnv ge.genv_cenv (envP0 b1 b2) = [(b1, 0, 256), (b2, 0, 256)] := by
  rw [hcenv]; rfl

macro "envgetP0" : tactic =>
  `(tactic| (unfold envP0; repeat (first
      | exact PTree.gss _ _ _
      | exact PTree.gempty _
      | refine (PTree.gso _ _ _ _ (by decide)).trans ?_)))

theorem WQ_ret {c : Ctx} {b1 b2 : Block} {hp : Heap} (hcl : c.cl - 1 < 256)
    (h : WQ c b1 b2 hp) : (Hc c ∗ Locs [(b1, 256), (b2, 256)]) hp := by
  obtain ⟨h1, h2, d, rfl, hc, h3, h4, d2, rfl, a3, h5, h6, d3, rfl, a5, he⟩ := h
  exact ⟨h1, _, d, rfl, hc, h3, _, d2, rfl, a3, h5, h6, d3, rfl, arr_join hcl a5, he⟩

theorem cenv_same : Deb2026_8924_d0.prog.prog_comp_env = Deb2026_8924_d1.prog.prog_comp_env := rfl

set_option maxHeartbeats 40000000 in
theorem ps_body_before (ge : CGenv) (c : Ctx) (acc : Integers.Int)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hdl1 : 2 ≤ c.dl) (hdl2 : c.dl < 256) (hcl1 : 2 ≤ c.cl) (hcl2 : c.cl < 256)
    (hacc : Integers.Int.eq acc Integers.Int.zero = false)
    (X : ExtP0 ge c acc) :
    Triple ge (FunctionEntry2 ge) f_is_public_suffix (PbodyP0 c) f_is_public_suffix.fn_body
      (RR (psSpecB c).post Sep.Assn.no) := by
  have hcenv1 := hcenv.trans cenv_same
  refine Sep.triple_exists ge _ _ _ _ _ (fun bs => ?_)
  obtain ⟨b1, b2⟩ := bs
  refine Case1C.triple_pure ge _ _ _ _ _ _ (fun hne => ?_)
  change Triple _ _ _ (LocalSt (envP0 b1 b2) (lP0 c) (W0 c b1 b2)) _ _
  have hcl' : c.cl - 1 < 256 := by omega
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_nop_loop ge _ _ _) ?_
  refine triple_seq ge _ _ _ (LocalSt (envP0 b1 b2) [] (Hc c ∗ Locs [(b1, 256), (b2, 256)])) _ _ _ ?main ?ret
  case ret =>
    refine Case3C.ret_locs ge _ _ (envP0 b1 b2) _ (Hc c) [(b1, 256), (b2, 256)] _
      (.Vint (Integers.Int.repr 0)) (.Vint (Integers.Int.repr 0)) _ (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)
      (fun _ => rfl) ?_ ?_ (fun hp hH => ⟨rfl, hH⟩)
    · rw [blocks_envP0 ge hcenv1]
      intro x hx'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'
      rcases hx' with rfl | rfl
      · exact ⟨b1, 256, rfl, by simp⟩
      · exact ⟨b2, 256, rfl, by simp⟩
    · rw [blocks_envP0 ge hcenv1]
      simp [hne]
  case main =>
  -- if(data && (domain && co->domain && !Curl_host_is_ipnum(co->domain)))
  refine triple_seq_fwd ge _ _ _ ?Q1 _ _ _ ?a1 ?a2
  case a1 =>
    refine triple_if_local ge _ _ (envP0 b1 b2) _ (W0 c b1 b2) _ true _ _ _
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ (.Vptr c.dB c.dO) (hT.get (by temps_get)),
        boolVal_ptrT _ (validC hH hag 0 (by simp) rfl hpn)⟩) ?_
    rw [if_pos rfl]
    refine triple_seq_fwd ge _ _ _ ?Q2 _ _ _ ?c1 ?c2
    case c1 =>
      refine triple_if_local ge _ _ (envP0 b1 b2) _ (W0 c b1 b2) _ true _ _ _
        (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ (.Vptr c.mB c.mO) (hT.get (by temps_get)),
          boolVal_ptrT _ (validC hH hag 2 (by simp) rfl hpn)⟩) ?_
      rw [if_pos rfl]
      refine triple_seq_fwd ge _ _ _ ?Q3 _ _ _ ?d1 ?d2
      case d1 =>
        refine triple_set_local_fwd ge _ _ (envP0 b1 b2) _ (W0 c b1 b2) _ _ (.Vptr c.kB c.kO) ?_
        intro le m hp hT hH hag
        exact eval_field (hT.get (by temps_get)) (hcenv1 ▸ co_ck) (hcenv1 ▸ off_dom) rfl
          (ldC hH hag 1 (by simp) rfl hpr)
      case d2 =>
        refine triple_set_local_fwd ge _ _ (envP0 b1 b2) _ (W0 c b1 b2) _ _ (Val.ofBool true) ?_
        intro le m hp hT hH hag
        exact EvalExpr.Ecast _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vptr c.kB c.kO) (hT.get (by temps_get)))
          (cast_bool_ptr (validC hH hag 4 (by simp) rfl hpn))
    case c2 =>
      refine triple_if_local ge _ _ (envP0 b1 b2) _ (W0 c b1 b2) _ true _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool true) (hT.get (by temps_get)), rfl⟩) ?_
      rw [if_pos rfl]
      refine triple_seq_fwd ge _ _ _ ?Q4 _ _ _ ?e1 ?e2
      case e1 =>
        refine triple_seq_fwd ge _ _ _ ?Q5 _ _ _ ?f1 ?f2
        case f1 =>
          refine triple_seq_fwd ge _ _ _ ?Q6 _ _ _ ?g1 ?g2
          case g1 =>
            refine triple_set_local_fwd ge _ _ (envP0 b1 b2) _ (W0 c b1 b2) _ _ (.Vptr c.kB c.kO) ?_
            intro le m hp hT hH hag
            exact eval_field (hT.get (by temps_get)) (hcenv1 ▸ co_ck) (hcenv1 ▸ off_dom) rfl
              (ldC hH hag 1 (by simp) rfl hpr)
          case g2 =>
            refine callS_some ge _ _ _ (W0 c b1 b2) (W0 c b1 b2) (Val.ofBool false) _ _ _ (envP0 b1 b2) _
              [.Vptr c.kB c.kO] X.ip.b X.fdI (X.sI b1 b2) X.ip.fp X.tI ?_ ?_ ?_
              (fun hp hK => hK) (fun v hp h => ⟨h.1 _ rfl, h.2⟩)
            · rfl
            · intro _ _ _; exact eval_callee_global (by envgetP0) X.ip.sym rfl
            intro le m hT
            exact EvalExprlist.cons _ _ _ _ _ _ _
              (EvalExpr.Etempvar _ _ (.Vptr c.kB c.kO) (hT.get (by temps_get))) rfl EvalExprlist.nil
        case f2 =>
          refine triple_set_local_fwd ge _ _ (envP0 b1 b2) _ (W0 c b1 b2) _ _ (Val.ofBool true) ?_
          intro le m hp hT _ _
          exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Eunop _ _ _ _ _
            (EvalExpr.Etempvar _ _ (Val.ofBool false) (hT.get (by temps_get))) rfl) rfl
      case e2 =>
        refine triple_set_local_fwd ge _ _ (envP0 b1 b2) _ (W0 c b1 b2) _ _ (Val.ofBool true) ?_
        intro le m hp hT _ _
        exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ (Val.ofBool true) (hT.get (by temps_get))) rfl
  case a2 =>
  refine triple_if_local ge _ _ (envP0 b1 b2) _ (W0 c b1 b2) _ true _ _ _
    (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool true) (hT.get (by temps_get)), rfl⟩) ?_
  rw [if_pos rfl]
  -- acceptable = FALSE; dlen = strlen(domain); clen = strlen(co->domain);
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envP0 b1 b2) _ (W0 c b1 b2) _ _ (Val.ofBool false)
      (fun _ _ _ _ _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (callS_some ge _ _ _ (W0 c b1 b2) (W0 c b1 b2) (.Vlong (r64 c.dl)) _ _ _ (envP0 b1 b2) _
        [.Vptr c.mB c.mO] X.sl.b X.fdS (X.sS1 b1 b2) X.sl.fp X.tS rfl
        (fun _ _ _ => eval_callee_global (by envgetP0) X.sl.sym rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vptr c.mB c.mO) (hT.get (by temps_get))) rfl EvalExprlist.nil)
        (fun hp hK => ⟨rfl, hK⟩) (fun v hp h => h))
      (triple_set_local_fwd ge _ _ (envP0 b1 b2) _ (W0 c b1 b2) _ _ (.Vlong (r64 c.dl))
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ (envP0 b1 b2) _ (W0 c b1 b2) _ _ (.Vptr c.kB c.kO)
          (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv1 ▸ co_ck) (hcenv1 ▸ off_dom) rfl (ldC hH hag 1 (by simp) rfl hpr)))
        (callS_some ge _ _ _ (W0 c b1 b2) (W0 c b1 b2) (.Vlong (r64 c.cl)) _ _ _ (envP0 b1 b2) _
          [.Vptr c.kB c.kO] X.sl.b X.fdS (X.sS2 b1 b2) X.sl.fp X.tS rfl
          (fun _ _ _ => eval_callee_global (by envgetP0) X.sl.sym rfl)
          (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ (.Vptr c.kB c.kO) (hT.get (by temps_get))) rfl EvalExprlist.nil)
          (fun hp hK => ⟨rfl, hK⟩) (fun v hp h => h)))
      (triple_set_local_fwd ge _ _ (envP0 b1 b2) _ (W0 c b1 b2) _ _ (.Vlong (r64 c.cl))
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))) ?_
  -- if((dlen < sizeof(lcase)) && (clen < sizeof(lcookie)))（修正前は末尾の '.' を取り除かない）
  refine triple_seq_fwd ge _ _ _ (LocalSt (envP0 b1 b2)
    [(_acceptable, Val.ofBool (!Integers.Int.eq acc Integers.Int.zero))] (WQ c b1 b2)) _ _ _ ?sz ?fin
  case sz =>
    refine triple_seq_fwd ge _ _ _ ?Qs _ _ _ ?s1 ?s2
    case s1 =>
      refine triple_if_local ge _ _ (envP0 b1 b2) _ (W0 c b1 b2) _ true _ _ _
        (fun le m hp hT _ _ => ⟨Val.ofBool true, EvalExpr.Ebinop _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vlong (r64 c.dl)) (hT.get (by temps_get)))
          (EvalExpr.Esizeof _ _) (ltS _ _ _ hdl2), rfl⟩) ?_
      rw [if_pos rfl]
      refine triple_set_local_fwd ge _ _ (envP0 b1 b2) _ (W0 c b1 b2) _ _ (Val.ofBool true) ?_
      intro le m hp hT _ _
      exact EvalExpr.Ecast _ _ (Val.ofBool true) _ (EvalExpr.Ebinop _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vlong (r64 c.cl)) (hT.get (by temps_get)))
          (EvalExpr.Esizeof _ _) (ltS _ _ _ hcl2)) rfl
    case s2 =>
    refine triple_if_local ge _ _ (envP0 b1 b2) _ (W0 c b1 b2) _ true _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool true) (hT.get (by temps_get)), rfl⟩) ?_
    rw [if_pos rfl]
    refine triple_seq_fwd ge _ _ _ ?Qp _ _ _ ?p1 ?p2
    case p1 =>
      refine triple_seq_fwd ge _ _ _ ?Qp1 _ _ _ ?q1 ?q2
      case q1 =>
        refine callS_some ge _ _ _ (W0 c b1 b2) (W0 c b1 b2) (.Vptr c.pB c.pO) _ _ _ (envP0 b1 b2) _
          [.Vptr c.dB c.dO] X.pu.b X.fdU (X.sU b1 b2) X.pu.fp X.tU ?_ ?_ ?_
          (fun hp hK => hK) (fun v hp h => ⟨h.1 _ rfl, h.2⟩)
        · rfl
        · intro _ _ _; exact eval_callee_global (by envgetP0) X.pu.sym rfl
        intro le m hT
        exact EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vptr c.dB c.dO) (hT.get (by temps_get))) rfl EvalExprlist.nil
      case q2 =>
        refine triple_set_local_fwd ge _ _ (envP0 b1 b2) _ (W0 c b1 b2) _ _ (.Vptr c.pB c.pO) ?_
        intro le m hp hT _ _
        exact EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))
    case p2 =>
    refine triple_if_local ge _ _ (envP0 b1 b2) _ (W0 c b1 b2) _ true _ _ _
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ (.Vptr c.pB c.pO) (hT.get (by temps_get)),
        boolVal_ptrT _ (validC hH hag 6 (by simp) rfl hpn)⟩) ?_
    -- Curl_strntolower(lcase, domain, dlen + 1);
    refine triple_seq_fwd ge _ _ _ ?Qi1 _ _ _ ?i1 ?i2
    case i1 =>
      refine callK_none ge _ _ sltTy tvoid cc_default (W0 c b1 b2) (W0 c b1 b2) none _ _ (envP0 b1 b2) _
        [.Vptr b1 Integers.Ptrofs.zero, .Vptr c.mB c.mO,
         .Vlong (Integers.Int64.add (r64 c.dl) (Integers.Int64.repr (Integers.Int.signed (Integers.Int.repr 1))))]
        X.lw.b X.fdL (X.sL1 b1 b2) X.lw.fp X.tL ?_ ?_ ?_
      · rfl
      · intro _ _ _; exact eval_callee_global (by envgetP0) X.lw.sym rfl
      intro le m hT
      exact EvalExprlist.cons _ _ _ _ _ _ _ (eval_arr (by envgetP0)) rfl
        (EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vptr c.mB c.mO) (hT.get (by temps_get))) rfl
          (EvalExprlist.cons _ _ _ _ _ _ _
            (EvalExpr.Ebinop _ _ _ _ _ _ _
              (EvalExpr.Etempvar _ _ (.Vlong (r64 c.dl)) (hT.get (by temps_get)))
              (EvalExpr.Econst_int _ _) rfl) rfl EvalExprlist.nil))
    case i2 =>
    -- Curl_strntolower(lcookie, co->domain, clen + 1);
    refine triple_seq_fwd ge _ _ _ ?Qk1 _ _ _ ?k1 ?k2
    case k1 =>
      refine triple_seq_fwd ge _ _ _ ?Qk2 _ _ _ ?l1 ?l2
      case l1 =>
        refine triple_set_local_fwd ge _ _ (envP0 b1 b2) _ (W0 c b1 b2) _ _ (.Vptr c.kB c.kO) ?_
        intro le m hp hT hH hag
        exact eval_field (hT.get (by temps_get)) (hcenv1 ▸ co_ck) (hcenv1 ▸ off_dom) rfl
          (ldC hH hag 1 (by simp) rfl hpr)
      case l2 =>
        refine callK_none ge _ _ sltTy tvoid cc_default (W0 c b1 b2) (WQ c b1 b2) none _ _ (envP0 b1 b2) _
          [.Vptr b2 Integers.Ptrofs.zero, .Vptr c.kB c.kO,
           .Vlong (Integers.Int64.add (r64 c.cl) (Integers.Int64.repr (Integers.Int.signed (Integers.Int.repr 1))))]
          X.lw.b X.fdL (X.sL2 b1 b2) X.lw.fp X.tL ?_ ?_ ?_
        · rfl
        · intro _ _ _; exact eval_callee_global (by envgetP0) X.lw.sym rfl
        intro le m hT
        exact EvalExprlist.cons _ _ _ _ _ _ _ (eval_arr (by envgetP0)) rfl
          (EvalExprlist.cons _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ (.Vptr c.kB c.kO) (hT.get (by temps_get))) rfl
            (EvalExprlist.cons _ _ _ _ _ _ _
              (EvalExpr.Ebinop _ _ _ _ _ _ _
                (EvalExpr.Etempvar _ _ (.Vlong (r64 c.cl)) (hT.get (by temps_get)))
                (EvalExpr.Econst_int _ _) rfl) rfl EvalExprlist.nil))
    case k2 =>
    -- acceptable = psl_is_cookie_domain_acceptable(psl, lcase, lcookie); Curl_psl_release(data);
    refine triple_seq_fwd ge _ _ _ ?Qn1 _ _ _ ?n1 ?n2
    case n1 =>
      refine triple_seq_fwd ge _ _ _ ?Qn2 _ _ _ ?o1 ?o2
      case o1 =>
        refine callS_some ge _ _ _ (WQ c b1 b2) (WQ c b1 b2) (.Vint acc) _ _ _ (envP0 b1 b2) _
          [.Vptr c.pB c.pO, .Vptr b1 Integers.Ptrofs.zero, .Vptr b2 Integers.Ptrofs.zero]
          X.ps.b X.fdP (X.sP b1 b2) X.ps.fp X.tP ?_ ?_ ?_ (fun hp hK => hK) (fun v hp h => h)
        · rfl
        · intro _ _ _; exact eval_callee_global (by envgetP0) X.ps.sym rfl
        intro le m hT
        exact EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vptr c.pB c.pO) (hT.get (by temps_get))) rfl
          (EvalExprlist.cons _ _ _ _ _ _ _ (eval_arr (by envgetP0)) rfl
            (EvalExprlist.cons _ _ _ _ _ _ _ (eval_arr (by envgetP0)) rfl EvalExprlist.nil))
      case o2 =>
        refine triple_set_local_fwd ge _ _ (envP0 b1 b2) _ (WQ c b1 b2) _ _
          (Val.ofBool (!Integers.Int.eq acc Integers.Int.zero)) ?_
        intro le m hp hT _ _
        exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ (.Vint acc) (hT.get (by temps_get)))
          (cast_int_bool _ m)
    case n2 =>
      refine weaken ge _ _ (callK_none ge _ _ [tptr (Ty.Tstruct _Curl_easy noattr)] tvoid cc_default
        (WQ c b1 b2) (WQ c b1 b2) none _ _ (envP0 b1 b2) _ [.Vptr c.dB c.dO]
        X.pr.b X.fdR (X.sR b1 b2) X.pr.fp X.tR ?_ ?_ ?_) (by subt)
      · rfl
      · intro _ _ _; exact eval_callee_global (by envgetP0) X.pr.sym rfl
      intro le m hT
      exact EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ (.Vptr c.dB c.dO) (hT.get (by temps_get))) rfl EvalExprlist.nil
  case fin =>
  -- if(!acceptable) …（libpsl が受け入れたので通らない）
  refine triple_if_local ge _ _ (envP0 b1 b2) _ (WQ c b1 b2) _ false _ _ _
    (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
      (EvalExpr.Etempvar _ _ (Val.ofBool (!Integers.Int.eq acc Integers.Int.zero)) (hT.get (by temps_get)))
      (notbool_ofBool _ m), (boolVal_ofBool_int _ m).trans (by rw [hacc]; rfl)⟩) ?_
  rw [if_neg Bool.false_ne_true]
  exact triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x)
    (fun _ _ _ ⟨he, _, hW⟩ => ⟨he, TempsHold_nil _, WQ_ret hcl' hW⟩)
    (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)

/-! ## 関数全体 -/

/-- **P0（D0）**: パッチを当てる前の `is_public_suffix` は、`lcookie` の `cl-1` 番目が `.` のまま PSL の検査に渡し、
libpsl が受け入れると CERR_OK を返す（Cookie を捨てない）。 -/
theorem ps_before (ge : CGenv) (c : Ctx) (acc : Integers.Int)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hdl1 : 2 ≤ c.dl) (hdl2 : c.dl < 256) (hcl1 : 2 ≤ c.cl) (hcl2 : c.cl < 256)
    (hacc : Integers.Int.eq acc Integers.Int.zero = false)
    (X : ExtP0 ge c acc) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_is_public_suffix) (psSpecB c) vs := by
  by_cases hvs : vs = argsP c
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  have hnv : listNorepet (varNames f_is_public_suffix.fn_vars) := by decide
  have hnp : listNorepet (varNames f_is_public_suffix.fn_params) := by decide
  have hdisj : listDisjoint (varNames f_is_public_suffix.fn_params)
      (varNames f_is_public_suffix.fn_temps) := by decide
  refine satisfies_internal ge (FunctionEntry2 ge) f_is_public_suffix _ _ (PbodyP0 c)
    (fun m hp hf hpre hd hag => ?_)
    (ps_body_before ge c acc hcenv hpr hpn hdl1 hdl2 hcl1 hcl2 hacc X)
  let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv (tarray tschar 256))
  let a2 := Mem.alloc a1.1 0 (sizeof ge.genv_cenv (tarray tschar 256))
  have hav : AllocVariables ge.genv_cenv emptyEnv m f_is_public_suffix.fn_vars (envP0 a1.2 a2.2) a2.1 :=
    .cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _))
  obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav hnv
    (by
      intro v hv
      simp only [f_is_public_suffix, List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl <;> rw [hcenv] <;> decide)
    (Heap.union hp hf) hag
  have hL : Locs [(a1.2, 256), (a2.2, 256)] hl := by
    have := Case3C.locs_of_localsAt ge.genv_cenv _ _ hl hloc
    rw [hcenv] at this
    exact this
  obtain ⟨dph, dfh⟩ := Heap.disjoint_union_left.mp hdl
  refine ⟨envP0 a1.2 a2.2,
    PTree.set _domain (.Vptr c.mB c.mO) (PTree.set _co (.Vptr c.coB c.coO)
      (PTree.set _data (.Vptr c.dB c.dO) (createUndefTemps f_is_public_suffix.fn_temps))),
    a2.1, hl, FunctionEntry2.intro hnv hnp hdisj hav rfl,
    Heap.disjoint_union_left.mpr ⟨hd, Heap.disjoint_comm dfh⟩, ?_, ?_⟩
  · rw [Heap.union_assoc, Heap.union_comm (Heap.disjoint_comm dfh), ← Heap.union_assoc]
    exact hagl
  · have hne : a1.2 ≠ a2.2 := by
      obtain ⟨h1, _, d1, rfl, x1, h2, _, d2, rfl, x2, _⟩ := hL
      exact Case3C.anyBytes_ne x1 x2 (by
        rw [Heap.disjoint_union_right] at d1; exact d1.1) (by decide) (by decide)
    refine ⟨(a1.2, a2.2), hne, rfl, ?_, ⟨hp, hl, dph, rfl, hpre.2, hL⟩⟩
    exact TempsHold_cons ((PTree.gss _ _ _))
      (TempsHold_cons ((PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _))
        (TempsHold_cons ((PTree.gso _ _ _ _ (by decide)).trans ((PTree.gso _ _ _ _ (by decide)).trans
          (PTree.gss _ _ _))) (TempsHold_nil _)))

end Deb2026_8924D
