/-
CVE-2025-10148: curl 8.14.1（D0、Debian のパッチを当てる前）の `ws_enc_write_head`。

証明すること（`write_head_before`、P0）: U0（`Deb2025_10148Before.lean` の `add_frame_before`）と同じ形。`Curl_rand` を呼ばず
（外部関数の仮定 `ExtDB` に `Curl_rand` が無い）、`Curl_bufq_write` に渡すヘッダの最後の4バイトは入口の `enc->mask` の `m0`、
戻ったあとも `enc->mask` は `m0`。`P0_C_debian` は、前提を満たす入口のメモリがあることも示す。

証明は D1（`Deb2025_10148DebAfter.lean`）の各文の証明を写し、一時変数の番号と、`Curl_rand` の2文（D1 の 13・14 番目）を
除いたことに合わせて直したもの（U1 から U0 を作ったのと同じ手順）。
-/
import Deb2025_10148DebAfter
import Deb2025_10148Before
import GenDeb2025_10148DebBefore
open CC CC.Sep CC.HProp
open Deb2025_10148_deb_before
open Case5C (RR boolVal_ofBool_tint)
open Case4debC (IsPtr cast_ptr)
open Deb2026_3805C (call2 set2 call_none heap_eq heap_imp triple_lift temps_weak once_loop int_eq_false ex_map)

set_option maxRecDepth 20000
set_option maxHeartbeats 400000

namespace Deb2025_10148C

theorem cenv_deb_before_same : Deb2025_10148_deb_before.prog.prog_comp_env
    = Deb2025_10148_up_after.prog.prog_comp_env := rfl

abbrev FD0 : Function := Deb2025_10148_deb_before.f_ws_enc_write_head
abbrev BD0 : Stmt := Deb2025_10148_deb_before.f_ws_enc_write_head.fn_body

/-- ヘッダの組み立ては U1 と同じ文。 -/
theorem hdr_same_d0 : hdS (sp 10 BD0) = hdS (sp 10 B1) := rfl

macro "unfD0" : tactic => `(tactic| (conv => arg 5; dsimp only [Deb2025_10148C.hdS, Deb2025_10148C.sp,
  Deb2025_10148C.BD0, Deb2025_10148_deb_before.f_ws_enc_write_head]))

/-- 事後条件（D0）: `*enc` と `*err` の所有を返し、`mask` は入口の `m0` のまま。戻り値は問わない。 -/
def postDB (c : Ctx) (errB : Block) : Val → HProp := fun _ hp =>
  (encPost c.encB (mk0 c) ∗ AB errB 0 4) hp

theorem post_BD (c : Ctx) (errB : Block) (wd : HProp)
    (hwd : ∀ h, wd h → AB c.encB 24 4 h) (v : Val) (hp : Heap)
    (h : (encA c.encB (mk0 c) wd ∗ AB errB 0 4) hp) : postDB c errB v hp :=
  sep_imp_l (fun h x => post_B c wd hwd v h x) h

/-- 出口（D0）: `mask` は `m0` のまま。 -/
theorem fin_heapDB (c : Ctx) (errB hb : Block) (hp : Heap)
    (h : ((AB hb 0 14 ∗ AB errB 0 4) ∗ K18D c c.m0) hp) :
    (encPost c.encB (mk0 c) ∗ LUD errB hb) hp := by
  have e1 : (AB hb 0 14 ∗ AB errB 0 4) ∗ K18D c c.m0 = encPost c.encB (mk0 c) ∗ LUD errB hb := by acxD
  rw [e1] at h
  exact h

/-- 呼ばれる側の関数（D0）。`Curl_rand` は無い。`Curl_bufq_write` の前提の4バイトは `m0`。 -/
structure ExtDB (ge : CGenv) (encB : Block) (m0 : List MemVal) : Prop where
  fail : ∃ b fd, Genv.findSymbol ge.genv_genv _Curl_failf = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr easyT, tptr tschar] tvoid ccVar
    ∧ ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fd failSpec vs
  fb : ∃ b fd, Genv.findSymbol ge.genv_genv _ws_frame_flags2firstbyte = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr easyT, tuint, tbool, tptr tint] tuchar cc_default
    ∧ ∀ errB vs, SatisfiesAt ge (FunctionEntry2 ge) fd (fbSpecD errB) vs
  info : ∃ b fd, Genv.findSymbol ge.genv_genv _ws_enc_info = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr encT, tptr easyT, tptr tschar] tvoid cc_default
    ∧ ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fd infoSpec vs
  cpy : ∃ b fd, Genv.findSymbol ge.genv_genv _memcpy = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr tvoid, tptr tvoid, tulong] (tptr tvoid) cc_default
    ∧ ∀ hb n mb vs, SatisfiesAt ge (FunctionEntry2 ge) fd (cpySpec hb n encB mb) vs
  bufq : ∃ b fd, Genv.findSymbol ge.genv_genv _Curl_bufq_write = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr (Ty.Tstruct _bufq noattr), tptr tuchar, tulong, tptr tint] tlong cc_default
    ∧ ∀ hb n errB vs, SatisfiesAt ge (FunctionEntry2 ge) fd (bufqSpecD hb n m0 errB) vs
  lit3 : ∃ b, Genv.findSymbol ge.genv_genv ___stringlit_3 = some b
  lit4 : ∃ b, Genv.findSymbol ge.genv_genv ___stringlit_4 = some b
  lit5 : ∃ b, Genv.findSymbol ge.genv_genv ___stringlit_5 = some b
  lit6 : ∃ b, Genv.findSymbol ge.genv_genv ___stringlit_6 = some b

section
variable (ge : CGenv) (c : Ctx) (errB hb : Block)

def P0DB : Sep.Assn := LocalSt (envD hb) (LkD c errB) (encPre c ∗ LUD errB hb)

theorem s0DB :
    Triple ge (FunctionEntry2 ge) FD0 (P0DB c errB hb) (hdS (sp 0 BD0))
      (RR (postDB c errB) (P0DB c errB hb)) := by
  unfD0
  unfold P0DB
  refine post_to ge _ _ _ (set2 ge _ _ _ _ _ _firstbyte _ (.Vint Integers.Int.zero) (by lf)
    (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)) ?_
  exact fun e le hp ⟨he, hT, hH⟩ => ⟨he, TempsHold_mono (by ls) hT, hH⟩

theorem s1DB (hpl : Integers.Int64.lt c.pl (Integers.Int64.repr 0) = false) :
    Triple ge (FunctionEntry2 ge) FD0 (P0DB c errB hb) (hdS (sp 1 BD0))
      (RR (postDB c errB) (P0DB c errB hb)) := by
  unfD0
  unfold P0DB
  refine if_val ge _ _ _ _ _ _ false _ _ _ (Val.ofBool false) ?_ (fun m => boolVal_ofBool_tint _ m) ?_
  · intro le m hp hT _ _
    refine EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm)))
      (EvalExpr.Econst_int _ _) ?_
    show some (Val.ofBool (Integers.Int64.lt c.pl (Integers.Int64.repr 0))) = _
    rw [hpl]
  · exact skip_to ge _ _ _ _ _ (fun _ _ _ x => x)

def P3DB : Sep.Assn := LocalSt (envD hb) ((_t'11, .Vlong c.rem) :: LkD c errB)
  (encA c.encB (mk0 c) (wd32 c c.w) ∗ LUD errB hb)

theorem s2DB (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env)
    (hrem : Integers.Int64.lt (Integers.Int64.repr 0) c.rem = false) :
    Triple ge (FunctionEntry2 ge) FD0 (P0DB c errB hb) (hdS (sp 2 BD0))
      (RR (postDB c errB) (P3DB c errB hb)) := by
  unfD0
  unfold P0DB
  have he : encPre c ∗ LUD errB hb = mapsto .Mint64 .Freeable c.encB 8 (.Vlong c.rem)
      ∗ (AB c.encB 0 8 ∗ AB c.encB 16 4 ∗ mk0 c ∗ wd32 c c.w ∗ LUD errB hb) := by
    unfold encPre; acxD
  refine triple_seq_fwd ge _ _ _
    (LocalSt (envD hb) ((_t'11, .Vlong c.rem) :: LkD c errB) (encPre c ∗ LUD errB hb)) _ _ _ ?_ ?_
  · refine set2 ge _ _ _ _ _ _t'11 _ (.Vlong c.rem) (by lf) ?_
    intro le m hp hT hH hag
    refine EvalExpr.Elvalue _ _ _ .Full _ (lv_enc hcenv (hT.get (by lm)) off_rem)
      (DerefLoc.value .Mint64 _ rfl ?_)
    show Mem.load .Mint64 m c.encB 8 = _
    exact cell_ld he hH hag
  · refine if_val ge _ _ _ _ _ _ false _ _ _ (Val.ofBool false) ?_ (fun m => boolVal_ofBool_tint _ m) ?_
    · intro le m hp hT _ _
      refine EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm)))
        (EvalExpr.Econst_int _ _) ?_
      show some (Val.ofBool (Integers.Int64.lt (Integers.Int64.repr 0) c.rem)) = _
      rw [hrem]
    · refine skip_to ge _ _ _ _ _ (fun e le hp ⟨he', hT, hH⟩ => ⟨he', hT, ?_⟩)
      rw [he] at hH
      exact conv1 (P' := AB c.encB 8 8) (fun _ x => mapsto_anyB x) (by acxD) hH

/-- `ws_frame_flags2firstbyte` のあと: `firstbyte` は戻り値の1バイト、`*err` は何かのコード。 -/
def P4DB : Sep.Assn := fun e le hp => ∃ x code,
  LocalSt (envD hb) ((_firstbyte, .Vint (Integers.Int.zero_ext 8 x)) :: (_t'1, .Vint x)
      :: (_t'10, cfV c) :: (_t'11, .Vlong c.rem) :: LkD c errB)
    (mapsto .Mint32 .Freeable errB 0 (.Vint code) ∗ K4D c hb) e le hp

theorem s3DB (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (X : ExtDB ge c.encB c.m0) (hdata : IsPtr c.dataV) :
    Triple ge (FunctionEntry2 ge) FD0 (P3DB c errB hb) (hdS (sp 3 BD0))
      (RR (postDB c errB) (P4DB c errB hb)) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.fb
  refine only_RR _ _ _ _ ?_
  unfD0
  unfold P3DB
  have hw : encA c.encB (mk0 c) (wd32 c c.w) ∗ LUD errB hb = wd32 c c.w
      ∗ (AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ mk0 c ∗ LUD errB hb) := by acxD
  have hf : encA c.encB (mk0 c) (wd32 c c.w) ∗ LUD errB hb = AB errB 0 4 ∗ K4D c hb := by
    acxD
  refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ v, LocalSt (envD hb)
      ((_t'1, v) :: (_t'10, cfV c) :: (_t'11, .Vlong c.rem) :: LkD c errB)
      ((fbSpecD errB).post v ∗ K4D c hb) e le hp) _ _ _ ?_ ?_
  · refine triple_seq_fwd ge _ _ _ (LocalSt (envD hb)
      ((_t'10, cfV c) :: (_t'11, .Vlong c.rem) :: LkD c errB)
      (encA c.encB (mk0 c) (wd32 c c.w) ∗ LUD errB hb)) _ _ _ ?_ ?_
    · refine set2 ge _ _ _ _ _ _t'10 _ (cfV c) (by lf) ?_
      intro le m hp hT hH hag
      exact Case5C.eval_bitfield (hT.get (by lm)) (hcenv ▸ co_enc) (hcenv ▸ off_cf) (by decide)
        (by decide) (by show Mem.load .Mint32 m c.encB 24 = _; exact cell_ld hw hH hag)
    · rw [hf]
      refine call2 ge _ _ (fbSpecD errB) _t'1 _ _ _ _ (AB errB 0 4) (K4D c hb)
        [c.dataV, .Vint c.fl, boolOf (cfV c), .Vptr errB Integers.Ptrofs.zero] bF fdF (hF errB) hfF htF
        ?hcl (by lf) ?hc ?ha ?hp
      case hcl => rfl
      case hc => exact fun _ _ _ => eval_callee_global rfl hsF rfl
      case ha =>
        intro le m hT
        eargs
      case hp =>
        intro h hh
        exact ⟨⟨_, _, _, rfl⟩, hh⟩
  · refine triple_lift ge _ _ (fun x : Val × Integers.Int × Integers.Int => fun e le hp => x.1 = .Vint x.2.1
      ∧ LocalSt (envD hb) ((_t'1, x.1) :: (_t'10, cfV c) :: (_t'11, .Vlong c.rem) :: LkD c errB)
        (mapsto .Mint32 .Freeable errB 0 (.Vint x.2.2) ∗ K4D c hb) e le hp) _ _ _ ?_ (fun ⟨v, x, code⟩ => ?_)
    · intro e le hp ⟨v, he, hT, h1, h2, hd, heq, ⟨x, code, hv, hm⟩, hk⟩
      exact ⟨(v, x, code), hv, he, hT, h1, h2, hd, heq, hm, hk⟩
    refine pure_l ge _ _ _ _ _ _ (fun hv => ?_)
    dsimp only at hv
    subst hv
    exact triple_conseq ge _ _ (set2 ge _ _ _ _ _ _firstbyte _ _ (by lf) (fun le m hp hT _ _ =>
        EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) rfl))
      (fun _ _ _ x => x) (fun e le hp h => ⟨x, code, h⟩)
      (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)

def P5DB : Sep.Assn := fun e le hp => ∃ x, LocalSt (envD hb) (L4D c errB x)
  (AB errB 0 4 ∗ K4D c hb) e le hp

theorem s4DB (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (hm0 : c.m0.length = 4) :
    Triple ge (FunctionEntry2 ge) FD0 (P4DB c errB hb) (hdS (sp 4 BD0))
      (RR (postDB c errB) (P5DB c errB hb)) := by
  unfD0
  refine triple_lift ge _ _ (fun y : Integers.Int × Integers.Int => LocalSt (envD hb)
      ((_firstbyte, .Vint (Integers.Int.zero_ext 8 y.1)) :: (_t'1, .Vint y.1)
        :: (_t'10, cfV c) :: (_t'11, .Vlong c.rem) :: LkD c errB)
      (mapsto .Mint32 .Freeable errB 0 (.Vint y.2) ∗ K4D c hb)) _ _ _
    (fun e le hp ⟨x, code, h⟩ => ⟨(x, code), h⟩) (fun ⟨x, code⟩ => ?_)
  refine triple_seq_fwd ge _ _ _ (LocalSt (envD hb) ((_t'9, .Vint code)
      :: (_firstbyte, .Vint (Integers.Int.zero_ext 8 x)) :: (_t'1, .Vint x)
        :: (_t'10, cfV c) :: (_t'11, .Vlong c.rem) :: LkD c errB)
      (mapsto .Mint32 .Freeable errB 0 (.Vint code) ∗ K4D c hb)) _ _ _ ?_ ?_
  · refine set2 ge _ _ _ _ _ _t'9 _ _ (by lf) (fun le m hp hT hH hag => ?_)
    refine EvalExpr.Elvalue _ _ _ .Full _ (lv_err (hT.get (by lm))) (DerefLoc.value .Mint32 _ rfl ?_)
    show Mem.load .Mint32 m errB 0 = _
    exact cell_ld rfl hH hag
  by_cases hr : code = Integers.Int.zero
  · subst hr
    refine if_val ge _ _ _ _ _ _ false _ _ _ (.Vint Integers.Int.zero)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (fun m => rfl) ?_
    exact skip_to ge _ _ _ _ _ (fun e le hp ⟨he, hT, hH⟩ => ⟨x, he, TempsHold_mono (by ls) hT,
      sep_imp_l (fun _ y => mapsto_anyB (chunk := .Mint32) y) hH⟩)
  · refine if_val ge _ _ _ _ _ _ true _ _ _ (.Vint code)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm)))
      (fun m => by show some (!Integers.Int.eq code Integers.Int.zero) = _; rw [int_eq_false hr]; rfl) ?_
    refine heap_imp ge _ _ _ _ _ (encA c.encB (mk0 c) (wd32 c c.w) ∗ LUD errB hb) _ _
      (fun hp h => conv1 (P' := AB errB 0 4) (fun _ y => mapsto_anyB (chunk := .Mint32) y) (by acxD) h) ?_
    exact retD ge _ _ hcenv errB hb _ _ _ _ _ _ _ (fun le m hT => by evx) (fun _ => by rfl)
      (fun hp h => post_BD c errB _ (fun _ x => mapsto_anyB x) _ hp h)

def P6DB : Sep.Assn := fun e le hp => ∃ x, LocalSt (envD hb) (L4D c errB x)
  (AB errB 0 4 ∗ K6D c hb) e le hp

theorem s5DB (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) :
    Triple ge (FunctionEntry2 ge) FD0 (P5DB c errB hb) (hdS (sp 5 BD0))
      (RR (postDB c errB) (P6DB c errB hb)) := by
  unfD0
  refine triple_lift ge _ _ (fun x => LocalSt (envD hb) (L4D c errB x)
    (AB errB 0 4 ∗ K4D c hb)) _ _ _ (fun e le hp h => h) (fun x => ?_)
  have hk : AB errB 0 4 ∗ K4D c hb = wd32 c c.w
      ∗ (AB errB 0 4 ∗ AB hb 0 14 ∗ AB c.encB 0 8
        ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ mk0 c) := by acxD
  refine if_both ge _ _ _ _ _ _ _ _ _ (fun le m hT => ⟨_, _, by evx, rfl⟩) ?_ ?_
  · refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ n, LocalSt (envD hb)
      ((_t'2, .Vint n) :: L4D c errB x)
      (AB errB 0 4 ∗ K4D c hb) e le hp) _ _ _ ?_ ?_
    · refine if_both ge _ _ _ _ _ _ _ _ _ (fun le m hT => ⟨_, _, by evx, rfl⟩) ?_ ?_
      · exact triple_conseq ge _ _ (set2 ge _ _ _ _ _ _t'2 _ (.Vint Integers.Int.one) (by lf)
          (fun le m hp hT _ _ => by evx)) (fun _ _ _ x => x) (fun _ _ _ x => ⟨_, x⟩)
          (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
      · exact triple_conseq ge _ _ (set2 ge _ _ _ _ _ _t'2 _ (.Vint Integers.Int.zero) (by lf)
          (fun le m hp hT _ _ => by evx)) (fun _ _ _ x => x) (fun _ _ _ x => ⟨_, x⟩)
          (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
    · refine triple_lift ge _ _ (fun n => LocalSt (envD hb)
        ((_t'2, .Vint n) :: L4D c errB x)
        (AB errB 0 4 ∗ K4D c hb)) _ _ _ (fun e le hp h => h)
        (fun n => ?_)
      rw [hk]
      refine post_to ge _ _ _ (store_bit ge _ _ _ _ _ _ _ c.encB _ 24 8 c.w rfl (by decide) (by decide) rfl
        (fun le m hT => lv_enc hcenv (hT.get (by lm)) off_cf)
        (fun le m hT => ⟨_, _, EvalExpr.Etempvar _ _ _ (hT.get (by lm)), rfl⟩)) ?_
      intro e le hp ⟨c', he, hT, hH⟩
      exact ⟨x, he, TempsHold_mono (by ls) hT,
        conv1 (P' := AB c.encB 24 4) (fun _ y => mapsto_anyB y) (by acxD) hH⟩
  · refine skip_to ge _ _ _ _ _ (fun e le hp ⟨he, hT, hH⟩ => ⟨x, he, hT, ?_⟩)
    rw [hk] at hH
    exact conv1 (P' := AB c.encB 24 4) (fun _ y => mapsto_anyB y) (by acxD) hH

theorem s6DB (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (X : ExtDB ge c.encB c.m0) (hdata : IsPtr c.dataV) (hm0 : c.m0.length = 4) :
    Triple ge (FunctionEntry2 ge) FD0 (P6DB c errB hb) (hdS (sp 6 BD0))
      (RR (postDB c errB) (P6DB c errB hb)) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.fail
  obtain ⟨bL, hsL⟩ := X.lit3
  unfD0
  refine triple_lift ge _ _ (fun x => LocalSt (envD hb) (L4D c errB x)
    (AB errB 0 4 ∗ K6D c hb)) _ _ _ (fun e le hp h => h) (fun x => ?_)
  refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ b : Bool, LocalSt (envD hb)
      ((_t'3, Val.ofBool b) :: L4D c errB x)
      (AB errB 0 4 ∗ K6D c hb) e le hp) _ _ _ ?_ ?_
  · refine if_both ge _ _ _ _ _ _ _ _ _ (fun le m hT => ⟨_, _, by evx, rfl⟩) ?_ ?_
    · refine triple_conseq ge _ _ (set2 ge _ _ _ _ _ _t'3 _
          (Val.ofBool (Integers.Int64.lt (Integers.Int64.repr (Integers.Int.signed (Integers.Int.repr 125))) c.pl))
          (by lf) (fun le m hp hT _ _ => ?_)) (fun _ _ _ x => x) (fun _ _ _ x => ⟨_, x⟩)
          (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
      exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm)))
        (EvalExpr.Econst_int _ _) rfl) (cast_bool_ofBool _ _)
    · exact triple_conseq ge _ _ (set2 ge _ _ _ _ _ _t'3 _ (Val.ofBool false) (by lf)
          (fun le m hp hT _ _ => EvalExpr.Econst_int _ _)) (fun _ _ _ x => x) (fun _ _ _ x => ⟨_, x⟩)
          (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
  · refine triple_lift ge _ _ (fun b : Bool => LocalSt (envD hb)
      ((_t'3, Val.ofBool b) :: L4D c errB x)
      (AB errB 0 4 ∗ K6D c hb)) _ _ _ (fun e le hp h => h)
      (fun b => ?_)
    refine if_val ge _ _ _ _ _ _ b _ _ _ (Val.ofBool b)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (fun m => boolVal_ofBool_tint _ m) ?_
    cases b
    · exact skip_to ge _ _ _ _ _ (fun e le hp ⟨he, hT, hH⟩ => ⟨x, he, TempsHold_mono (by ls) hT, hH⟩)
    · refine heap_eq ge _ _ _ _ _ (emp ∗ (AB errB 0 4 ∗ K6D c hb))
        _ _ (emp_l _) ?_
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (call_none ge _ _ failSpec _ _ _ _ emp _
        [c.dataV, .Vptr bL Integers.Ptrofs.zero] bF fdF hF hfF htF rfl
        (fun _ _ _ => eval_callee_global rfl hsF rfl) (fun le m hT => ?_) (fun _ h => h) (fun _ _ h => h)) ?_
      · refine EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (cast_ptr hdata _ _ _) ?_
        exact EvalExprlist.cons _ _ _ _ _ _ _ (eval_callee_global rfl hsL rfl) rfl EvalExprlist.nil
      · refine triple_seq_fwd ge _ _ _ _ _ _ _ (store_any ge _ _ _ _ _ _ _ .Mint32 errB _ 0 rfl rfl rfl
          (fun le m hT => lv_err (hT.get (by lm))) (fun le m hT => ⟨_, _, EvalExpr.Econst_int _ _, rfl⟩)) ?_
        refine heap_eq ge _ _ _ _ (AB errB 0 4 ∗ K6D c hb) (encA c.encB (mk0 c) (AB c.encB 24 4) ∗ LUD errB hb)
          _ _ (by acxD) ?_
        exact retD ge _ _ hcenv errB hb _ _ _ _ _ _ _ (fun le m hT => by evx) (fun _ => by rfl)
          (fun hp h => post_BD c errB _ (fun _ y => y) _ hp h)

theorem s7DB (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (X : ExtDB ge c.encB c.m0) (hdata : IsPtr c.dataV) (hm0 : c.m0.length = 4) :
    Triple ge (FunctionEntry2 ge) FD0 (P6DB c errB hb) (hdS (sp 7 BD0))
      (RR (postDB c errB) (P6DB c errB hb)) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.fail
  obtain ⟨bL, hsL⟩ := X.lit4
  unfD0
  refine triple_lift ge _ _ (fun x => LocalSt (envD hb) (L4D c errB x)
    (AB errB 0 4 ∗ K6D c hb)) _ _ _ (fun e le hp h => h) (fun x => ?_)
  refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ b : Bool, LocalSt (envD hb)
      ((_t'4, Val.ofBool b) :: L4D c errB x)
      (AB errB 0 4 ∗ K6D c hb) e le hp) _ _ _ ?_ ?_
  · refine if_both ge _ _ _ _ _ _ _ _ _ (fun le m hT => ⟨_, _, by evx, rfl⟩) ?_ ?_
    · refine triple_conseq ge _ _ (set2 ge _ _ _ _ _ _t'4 _
          (Val.ofBool (Integers.Int64.lt (Integers.Int64.repr (Integers.Int.signed (Integers.Int.repr 125))) c.pl))
          (by lf) (fun le m hp hT _ _ => ?_)) (fun _ _ _ x => x) (fun _ _ _ x => ⟨_, x⟩)
          (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
      exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm)))
        (EvalExpr.Econst_int _ _) rfl) (cast_bool_ofBool _ _)
    · exact triple_conseq ge _ _ (set2 ge _ _ _ _ _ _t'4 _ (Val.ofBool false) (by lf)
          (fun le m hp hT _ _ => EvalExpr.Econst_int _ _)) (fun _ _ _ x => x) (fun _ _ _ x => ⟨_, x⟩)
          (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
  · refine triple_lift ge _ _ (fun b : Bool => LocalSt (envD hb)
      ((_t'4, Val.ofBool b) :: L4D c errB x)
      (AB errB 0 4 ∗ K6D c hb)) _ _ _ (fun e le hp h => h)
      (fun b => ?_)
    refine if_val ge _ _ _ _ _ _ b _ _ _ (Val.ofBool b)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (fun m => boolVal_ofBool_tint _ m) ?_
    cases b
    · exact skip_to ge _ _ _ _ _ (fun e le hp ⟨he, hT, hH⟩ => ⟨x, he, TempsHold_mono (by ls) hT, hH⟩)
    · refine heap_eq ge _ _ _ _ _ (emp ∗ (AB errB 0 4 ∗ K6D c hb))
        _ _ (emp_l _) ?_
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (call_none ge _ _ failSpec _ _ _ _ emp _
        [c.dataV, .Vptr bL Integers.Ptrofs.zero] bF fdF hF hfF htF rfl
        (fun _ _ _ => eval_callee_global rfl hsF rfl) (fun le m hT => ?_) (fun _ h => h) (fun _ _ h => h)) ?_
      · refine EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (cast_ptr hdata _ _ _) ?_
        exact EvalExprlist.cons _ _ _ _ _ _ _ (eval_callee_global rfl hsL rfl) rfl EvalExprlist.nil
      · refine triple_seq_fwd ge _ _ _ _ _ _ _ (store_any ge _ _ _ _ _ _ _ .Mint32 errB _ 0 rfl rfl rfl
          (fun le m hT => lv_err (hT.get (by lm))) (fun le m hT => ⟨_, _, EvalExpr.Econst_int _ _, rfl⟩)) ?_
        refine heap_eq ge _ _ _ _ (AB errB 0 4 ∗ K6D c hb) (encA c.encB (mk0 c) (AB c.encB 24 4) ∗ LUD errB hb)
          _ _ (by acxD) ?_
        exact retD ge _ _ hcenv errB hb _ _ _ _ _ _ _ (fun le m hT => by evx) (fun _ => by rfl)
          (fun hp h => post_BD c errB _ (fun _ y => y) _ hp h)

theorem s8DB (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (X : ExtDB ge c.encB c.m0) (hdata : IsPtr c.dataV) (hm0 : c.m0.length = 4) :
    Triple ge (FunctionEntry2 ge) FD0 (P6DB c errB hb) (hdS (sp 8 BD0))
      (RR (postDB c errB) (P6DB c errB hb)) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.fail
  obtain ⟨bL, hsL⟩ := X.lit5
  unfD0
  refine triple_lift ge _ _ (fun x => LocalSt (envD hb) (L4D c errB x)
    (AB errB 0 4 ∗ K6D c hb)) _ _ _ (fun e le hp h => h) (fun x => ?_)
  refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ b : Bool, LocalSt (envD hb)
      ((_t'5, Val.ofBool b) :: L4D c errB x)
      (AB errB 0 4 ∗ K6D c hb) e le hp) _ _ _ ?_ ?_
  · refine if_both ge _ _ _ _ _ _ _ _ _ (fun le m hT => ⟨_, _, by evx, rfl⟩) ?_ ?_
    · refine triple_conseq ge _ _ (set2 ge _ _ _ _ _ _t'5 _
          (Val.ofBool (Integers.Int64.lt (Integers.Int64.repr (Integers.Int.signed (Integers.Int.repr 125))) c.pl))
          (by lf) (fun le m hp hT _ _ => ?_)) (fun _ _ _ x => x) (fun _ _ _ x => ⟨_, x⟩)
          (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
      exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm)))
        (EvalExpr.Econst_int _ _) rfl) (cast_bool_ofBool _ _)
    · exact triple_conseq ge _ _ (set2 ge _ _ _ _ _ _t'5 _ (Val.ofBool false) (by lf)
          (fun le m hp hT _ _ => EvalExpr.Econst_int _ _)) (fun _ _ _ x => x) (fun _ _ _ x => ⟨_, x⟩)
          (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
  · refine triple_lift ge _ _ (fun b : Bool => LocalSt (envD hb)
      ((_t'5, Val.ofBool b) :: L4D c errB x)
      (AB errB 0 4 ∗ K6D c hb)) _ _ _ (fun e le hp h => h)
      (fun b => ?_)
    refine if_val ge _ _ _ _ _ _ b _ _ _ (Val.ofBool b)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (fun m => boolVal_ofBool_tint _ m) ?_
    cases b
    · exact skip_to ge _ _ _ _ _ (fun e le hp ⟨he, hT, hH⟩ => ⟨x, he, TempsHold_mono (by ls) hT, hH⟩)
    · refine heap_eq ge _ _ _ _ _ (emp ∗ (AB errB 0 4 ∗ K6D c hb))
        _ _ (emp_l _) ?_
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (call_none ge _ _ failSpec _ _ _ _ emp _
        [c.dataV, .Vptr bL Integers.Ptrofs.zero] bF fdF hF hfF htF rfl
        (fun _ _ _ => eval_callee_global rfl hsF rfl) (fun le m hT => ?_) (fun _ h => h) (fun _ _ h => h)) ?_
      · refine EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (cast_ptr hdata _ _ _) ?_
        exact EvalExprlist.cons _ _ _ _ _ _ _ (eval_callee_global rfl hsL rfl) rfl EvalExprlist.nil
      · refine triple_seq_fwd ge _ _ _ _ _ _ _ (store_any ge _ _ _ _ _ _ _ .Mint32 errB _ 0 rfl rfl rfl
          (fun le m hT => lv_err (hT.get (by lm))) (fun le m hT => ⟨_, _, EvalExpr.Econst_int _ _, rfl⟩)) ?_
        refine heap_eq ge _ _ _ _ (AB errB 0 4 ∗ K6D c hb) (encA c.encB (mk0 c) (AB c.encB 24 4) ∗ LUD errB hb)
          _ _ (by acxD) ?_
        exact retD ge _ _ hcenv errB hb _ _ _ _ _ _ _ (fun le m hT => by evx) (fun _ => by rfl)
          (fun hp h => post_BD c errB _ (fun _ y => y) _ hp h)

def P10DB : Sep.Assn := LocalSt (envD hb) (LkD c errB) (LUD errB hb ∗ K10 c)

theorem s9DB (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) :
    Triple ge (FunctionEntry2 ge) FD0 (P6DB c errB hb) (hdS (sp 9 BD0))
      (RR (postDB c errB) (P10DB c errB hb)) := by
  unfD0
  refine triple_lift ge _ _ (fun x => LocalSt (envD hb) (L4D c errB x)
    (AB errB 0 4 ∗ K6D c hb)) _ _ _ (fun e le hp h => h) (fun x => ?_)
  refine only_RR _ _ _ _ ?_
  have h24 : AB errB 0 4 ∗ K6D c hb
      = AB c.encB 24 4 ∗ (AB errB 0 4 ∗ AB hb 0 14
        ∗ AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ mk0 c) := by acxD
  have hh : AB c.encB 24 4 ∗ (AB errB 0 4 ∗ AB hb 0 14
        ∗ AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ mk0 c)
      = AB hb 0 14 ∗ (AB errB 0 4 ∗ K10 c) := by
    acxD
  let L9 := (_t'6, Val.Vint (Integers.Int.zero_ext 8 (Integers.Int.zero_ext 8 x))) :: L4D c errB x
  refine triple_seq_fwd ge _ _ _ (LocalSt (envD hb) L9
    (AB c.encB 24 4 ∗ (AB errB 0 4 ∗ AB hb 0 14
        ∗ AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ mk0 c))) _ _ _ ?_ ?_
  · refine triple_seq_fwd ge _ _ _ (LocalSt (envD hb) L9
      (AB errB 0 4 ∗ K6D c hb)) _ _ _ ?_ ?_
    · exact set2 ge _ _ _ _ _ _t'6 _ _ (by lf) (fun le m hp hT _ _ =>
        EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) rfl)
    · rw [h24]
      exact store_byte ge _ _ _ _ _ _ _ c.encB _ 24 0 3 rfl rfl
        (fun le m hT => lv_enc hcenv (hT.get (by lm)) off_fb)
        (fun le m hT => ⟨_, _, EvalExpr.Etempvar _ _ _ (hT.get (by lm)), rfl⟩)
  · refine post_to ge _ _ _ (heap_eq ge _ _ _ _ _ _ _ _ hh
      (hstore ge _ _ _ _ _ hb (envD_head _) 0 13 rfl _ rfl
        (fun le m hT => ⟨_, _, EvalExpr.Etempvar _ _ _ (hT.get (by lm)), rfl⟩))) ?_
    intro e le hp ⟨he, hT, hH⟩
    refine ⟨he, TempsHold_mono (by ls) hT, ?_⟩
    rw [show LUD errB hb ∗ K10 c = AB hb 0 14 ∗ (AB errB 0 4 ∗ K10 c) by acxD]
    exact hH

def P11DB : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ LocalSt (envD hb) (L13D c errB n) (LUD errB hb ∗ K10 c) e le hp

theorem s10DB :
    Triple ge (FunctionEntry2 ge) FD0 (P10DB c errB hb) (hdS (sp 10 BD0))
      (RR (postDB c errB) (P11DB c errB hb)) := by
  rw [hdr_same_d0]
  unfold P10DB
  have hq : LUD errB hb ∗ K10 c = AB hb 0 14 ∗ (AB errB 0 4 ∗ K10 c) := by acxD
  rw [hq]
  refine temps_weak ge _ _ _ _ ((_payload_len, .Vlong c.pl) :: LkD c errB) _ _ _
    (by ls) ?_
  refine triple_conseq ge _ _ (hdr ge _ _ _ _ c.pl _ (postDB c errB) hb (envD_head _) (by lf))
    (fun _ _ _ x => x) ?_ (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
  intro e le hp ⟨n, hn, he, hT, hH⟩
  exact ⟨n, hn, he, TempsHold_mono (by ls) hT, by rw [hq]; exact hH⟩

/-- `P11DB` の `n` を取り出す。 -/
theorem lift_nDB (P : Nat → Sep.Assn) (s : Stmt) (R : Sep.ExitConds)
    (h : ∀ n, (n = 2 ∨ n = 4 ∨ n = 10) → Triple ge (FunctionEntry2 ge) FD0 (P n) s R) :
    Triple ge (FunctionEntry2 ge) FD0 (fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10) ∧ P n e le hp) s R := by
  intro k e le hp hf m hd hag ⟨n, hn, hP⟩
  exact h n hn k e le hp hf m hd hag hP

theorem s11DB (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) :
    Triple ge (FunctionEntry2 ge) FD0 (P11DB c errB hb) (hdS (sp 11 BD0))
      (RR (postDB c errB) (P11DB c errB hb)) := by
  unfD0
  refine lift_nDB ge _ _ _ (fun n hn => ?_)
  have h0 : LUD errB hb ∗ K10 c = AB c.encB 0 8 ∗ (AB errB 0 4 ∗ AB hb 0 14 ∗ AB c.encB 8 8
      ∗ AB c.encB 16 4 ∗ mk0 c ∗ AB c.encB 24 4) := by acxD
  have h8 : LUD errB hb ∗ K10 c = AB c.encB 8 8 ∗ (AB errB 0 4 ∗ AB hb 0 14 ∗ AB c.encB 0 8
      ∗ AB c.encB 16 4 ∗ mk0 c ∗ AB c.encB 24 4) := by acxD
  let l7 := (_t'7, Val.Vlong c.pl) :: L13D c errB n
  refine post_to ge _ _ _ (P := LocalSt (envD hb) (L13D c errB n) (LUD errB hb ∗ K10 c))
    (Q := LocalSt (envD hb) l7 (LUD errB hb ∗ K10 c)) ?_
    (fun e le hp ⟨he, hT, hH⟩ => ⟨n, hn, he, TempsHold_mono (by ls) hT, hH⟩)
  refine triple_seq_fwd ge _ _ _ (LocalSt (envD hb) l7 (LUD errB hb ∗ K10 c)) _ _ _ ?_ ?_
  · refine triple_seq_fwd ge _ _ _ (LocalSt (envD hb) l7 (LUD errB hb ∗ K10 c)) _ _ _
      (set2 ge _ _ _ _ _ _t'7 _ _ (by lf) (fun le m hp hT _ _ =>
        EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) rfl)) ?_
    rw [h0]
    exact store_any ge _ _ _ _ _ _ _ .Mint64 c.encB _ 0 rfl rfl rfl
      (fun le m hT => lv_enc hcenv (hT.get (by lm)) off_pl)
      (fun le m hT => ⟨_, _, EvalExpr.Etempvar _ _ _ (hT.get (by lm)), rfl⟩)
  · rw [h8]
    exact store_any ge _ _ _ _ _ _ _ .Mint64 c.encB _ 8 rfl rfl rfl
      (fun le m hT => lv_enc hcenv (hT.get (by lm)) off_rem)
      (fun le m hT => ⟨_, _, EvalExpr.Etempvar _ _ _ (hT.get (by lm)), rfl⟩)

theorem s12DB (X : ExtDB ge c.encB c.m0) (hdata : IsPtr c.dataV) :
    Triple ge (FunctionEntry2 ge) FD0 (P11DB c errB hb) (hdS (sp 12 BD0))
      (RR (postDB c errB) (P11DB c errB hb)) := by
  obtain ⟨bI, fdI, hsI, hfI, htI, hI⟩ := X.info
  obtain ⟨bL, hsL⟩ := X.lit6
  unfD0
  refine lift_nDB ge _ _ _ (fun n hn => ?_)
  refine post_to ge _ _ _ (P := LocalSt (envD hb) (L13D c errB n) (LUD errB hb ∗ K10 c))
    (Q := LocalSt (envD hb) (L13D c errB n) (LUD errB hb ∗ K10 c)) ?_
    (fun e le hp h => ⟨n, hn, h⟩)
  refine heap_eq ge _ _ _ _ _ (emp ∗ (LUD errB hb ∗ K10 c)) _ _ (emp_l _) ?_
  refine call_none ge _ _ infoSpec _ _ _ _ emp _
    [.Vptr c.encB Integers.Ptrofs.zero, c.dataV, .Vptr bL Integers.Ptrofs.zero] bI fdI hI hfI htI rfl
    (fun _ _ _ => eval_callee_global rfl hsI rfl) (fun le m hT => ?_) (fun _ h => h) (fun _ _ h => h)
  exact EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) rfl
    (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (cast_ptr hdata _ _ _)
    (EvalExprlist.cons _ _ _ _ _ _ _ (eval_callee_global rfl hsL rfl) rfl EvalExprlist.nil))

def P15DB  : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ ∃ v, LocalSt (envD hb) (L13D c errB n)
    ((cpySpec hb n c.encB c.m0).post v ∗ K15D c errB hb n) e le hp

theorem s13DB (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (X : ExtDB ge c.encB c.m0) :
    Triple ge (FunctionEntry2 ge) FD0 (P11DB c errB hb) (hdS (sp 13 BD0))
      (RR (postDB c errB) (P15DB c errB hb)) := by
  obtain ⟨bC, fdC, hsC, hfC, htC, hC⟩ := X.cpy
  unfD0
  refine lift_nDB ge _ _ _ (fun n hn => ?_)
  refine post_to ge _ _ _ (Q := fun e le hp => ∃ v, LocalSt (envD hb) (L13D c errB n)
    ((cpySpec hb n c.encB c.m0).post v ∗ K15D c errB hb n) e le hp) ?_ (fun e le hp h => ⟨n, hn, h⟩)
  have hq : LUD errB hb ∗ K10 c
      = (AB hb n 4 ∗ bytesPtsTo c.encB .Freeable 20 c.m0) ∗ K15D c errB hb n := by
    simp only [K10, LUD]; rw [head_split hb n (hn_le hn)]; acxD
  rw [hq]
  refine call_none_ex ge _ _ (cpySpec hb n c.encB c.m0) _ _ _ _ _ _ bC fdC (hC hb n c.m0) hfC htC rfl
    (fun _ _ _ => eval_callee_global rfl hsC rfl) (fun le m hT => ?_)
  have hl : (_hlen, Val.Vlong (Integers.Int64.repr n)) ∈ L13D c errB n := List.mem_cons_self ..
  rcases hn with rfl | rfl | rfl <;>
  · refine ⟨_, EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Elvalue _ _ _ _ _ (eval_var_local (envD_head _)) (DerefLoc.reference rfl))
        (EvalExpr.Etempvar _ _ _ (hT.get hl)) rfl) rfl
      (EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Eaddrof _ _ _ _ (lv_enc hcenv (hT.get (by lm)) off_mask)) rfl
      (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl EvalExprlist.nil)), ?_⟩
    exact fun h hh => ⟨⟨_, _, rfl, rfl, rfl⟩, hh⟩

def P16DB  : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ LocalSt (envD hb) (L16D c errB n)
    ((bytesPtsTo hb .Freeable n c.m0 ∗ bytesPtsTo c.encB .Freeable 20 c.m0) ∗ K15D c errB hb n) e le hp

theorem s14DB  :
    Triple ge (FunctionEntry2 ge) FD0 (P15DB c errB hb) (hdS (sp 14 BD0))
      (RR (postDB c errB) (P16DB c errB hb)) := by
  unfD0
  refine lift_nDB ge _ _ _ (fun n hn => ?_)
  refine triple_lift ge _ _ (fun v => LocalSt (envD hb) (L13D c errB n)
    ((cpySpec hb n c.encB c.m0).post v ∗ K15D c errB hb n)) _ _ _ (fun e le hp h => h) (fun v => ?_)
  refine post_to ge _ _ _ (triple_set_local ge _ _ _ (L13D c errB n) (LkD c errB) _ _hlen _
    (.Vlong (Integers.Int64.repr ((n : Z) + 4))) (by ls) (by lf) (fun le m hp hT _ _ => ?_)) ?_
  · refine EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..)))
      (EvalExpr.Econst_int _ _) ?_
    rcases hn with rfl | rfl | rfl <;> rfl
  · exact fun e le hp h => ⟨n, hn, h⟩

theorem s15DB (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env)  :
    Triple ge (FunctionEntry2 ge) FD0 (P16DB c errB hb) (hdS (sp 15 BD0))
      (RR (postDB c errB) (P16DB c errB hb)) := by
  unfD0
  refine lift_nDB ge _ _ _ (fun n hn => ?_)
  refine post_to ge _ _ _ ?_ (fun e le hp h => ⟨n, hn, h⟩)
  have hq : (bytesPtsTo hb .Freeable n c.m0 ∗ bytesPtsTo c.encB .Freeable 20 c.m0) ∗ K15D c errB hb n
      = AB c.encB 16 4 ∗ (bytesPtsTo hb .Freeable n c.m0 ∗ bytesPtsTo c.encB .Freeable 20 c.m0 ∗ AB hb 0 n
        ∗ AB hb ((n : Z) + 4) (10 - n) ∗ AB errB 0 4 ∗ AB c.encB 0 8 ∗ AB c.encB 8 8
        ∗ AB c.encB 24 4) := by acxD
  rw [hq]
  exact store_any ge _ _ _ _ _ _ _ .Mint32 c.encB _ 16 rfl rfl rfl
    (fun le m hT => lv_enc hcenv (hT.get (by lm)) off_xori)
    (fun le m hT => ⟨_, _, EvalExpr.Econst_int _ _, rfl⟩)

def P18DB  : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ ∃ v, LocalSt (envD hb) ((_n, v) :: (_t'8, v) :: L16D c errB n)
    ((bufqSpecD hb n c.m0 errB).post v ∗ K18D c c.m0) e le hp

theorem s16DB (X : ExtDB ge c.encB c.m0) (hout : IsPtr c.outV) :
    Triple ge (FunctionEntry2 ge) FD0 (P16DB c errB hb) (hdS (sp 16 BD0))
      (RR (postDB c errB) (P18DB c errB hb)) := by
  obtain ⟨bQ, fdQ, hsQ, hfQ, htQ, hQ⟩ := X.bufq
  unfD0
  refine lift_nDB ge _ _ _ (fun n hn => ?_)
  refine post_to ge _ _ _ (Q := fun e le hp => ∃ v, LocalSt (envD hb) ((_n, v) :: (_t'8, v) :: L16D c errB n)
    ((bufqSpecD hb n c.m0 errB).post v ∗ K18D c c.m0) e le hp) ?_ (fun e le hp h => ⟨n, hn, h⟩)
  have hq : (bytesPtsTo hb .Freeable n c.m0 ∗ bytesPtsTo c.encB .Freeable 20 c.m0) ∗ K15D c errB hb n
      = (AB hb 0 n ∗ bytesPtsTo hb .Freeable n c.m0 ∗ AB hb ((n : Z) + 4) (10 - n) ∗ AB errB 0 4)
        ∗ K18D c c.m0 := by acxD
  rw [hq]
  refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ v, LocalSt (envD hb) ((_t'8, v) :: L16D c errB n)
    ((bufqSpecD hb n c.m0 errB).post v ∗ K18D c c.m0) e le hp) _ _ _ ?_ ?_
  · refine call2 ge _ _ (bufqSpecD hb n c.m0 errB) _t'8 _ _ _ _ _ (K18D c c.m0)
      [c.outV, .Vptr hb Integers.Ptrofs.zero, .Vlong (Integers.Int64.repr ((n : Z) + 4)),
        .Vptr errB Integers.Ptrofs.zero] bQ fdQ (hQ hb n errB) hfQ htQ ?hcl (by lf) ?hc ?ha ?hp
    case hcl => rfl
    case hc => exact fun _ _ _ => eval_callee_global rfl hsQ rfl
    case ha =>
      intro le m hT
      exact EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (cast_ptr hout _ _ _)
        (EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Elvalue _ _ _ _ _ (eval_var_local (envD_head _)) (DerefLoc.reference rfl)) rfl
        (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..))) rfl
        (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) rfl
          EvalExprlist.nil)))
    case hp => exact fun h hh => ⟨⟨c.outV, rfl⟩, hh⟩
  · refine ex_map ge _ _ _ _ _ (fun v => ?_)
    exact set2 ge _ _ _ _ _ _n _ v (by lf)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm)))

def P19DB  : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ ∃ k, LocalSt (envD hb) ((_n, .Vlong k) :: L16D c errB n)
    ((AB hb 0 14 ∗ AB errB 0 4) ∗ K18D c c.m0) e le hp

theorem s17DB (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env)  :
    Triple ge (FunctionEntry2 ge) FD0 (P18DB c errB hb) (hdS (sp 17 BD0))
      (RR (postDB c errB) (P19DB c errB hb)) := by
  unfD0
  refine lift_nDB ge _ _ _ (fun n hn => ?_)
  refine triple_lift ge _ _ (fun x : Val × Integers.Int64 => fun e le hp => x.1 = .Vlong x.2
      ∧ LocalSt (envD hb) ((_n, x.1) :: (_t'8, x.1) :: L16D c errB n)
        ((AB hb 0 14 ∗ AB errB 0 4) ∗ K18D c c.m0) e le hp) _ _ _ ?_ (fun ⟨v, k⟩ => ?_)
  · intro e le hp ⟨v, he, hT, h1, h2, hd, heq, ⟨k, hv, hh⟩, hk⟩
    exact ⟨(v, k), hv, he, hT, h1, h2, hd, heq, hh, hk⟩
  refine pure_l ge _ _ _ _ _ _ (fun hv => ?_)
  dsimp only at hv
  subst hv
  refine if_both ge _ _ _ _ _ _ _ _ _ (fun le m hT =>
    ⟨Val.ofBool (Integers.Int64.lt k (Integers.Int64.repr (Integers.Int.signed (Integers.Int.repr 0)))), _,
      EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..)))
        (EvalExpr.Econst_int _ _) rfl, boolVal_ofBool_tint _ _⟩) ?_ ?_
  · refine heap_imp ge _ _ _ _ _ _ _ _ (fun hp h => fin_heapDB c errB hb hp h) ?_
    exact retD ge _ _ hcenv errB hb _ _ _ _ _ _ _ (fun le m hT => by evx) (fun _ => by rfl)
      (fun hp h => h)
  · exact skip_to ge _ _ _ _ _ (fun e le hp ⟨he, hT, hH⟩ => ⟨n, hn, k, he, TempsHold_mono (by ls) hT, hH⟩)

theorem s18DB (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env)  :
    Triple ge (FunctionEntry2 ge) FD0 (P19DB c errB hb) (hdS (sp 18 BD0))
      (RR (postDB c errB) (P19DB c errB hb)) := by
  unfD0
  refine lift_nDB ge _ _ _ (fun n hn => ?_)
  refine triple_lift ge _ _ (fun k => LocalSt (envD hb) ((_n, .Vlong k) :: L16D c errB n)
    ((AB hb 0 14 ∗ AB errB 0 4) ∗ K18D c c.m0)) _ _ _
    (fun e le hp h => h) (fun k => ?_)
  refine if_both ge _ _ _ _ _ _ _ _ _ (fun le m hT =>
    ⟨Val.ofBool (!Integers.Int64.eq k (Integers.Int64.repr ((n : Z) + 4))), _,
      EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..))) rfl)
        (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) rfl, boolVal_ofBool_tint _ _⟩) ?_ ?_
  · refine triple_seq_fwd ge _ _ _ _ _ _ _ (once_loop ge _ _ _ _ _ (triple_skip ge _ _ _)) ?_
    refine heap_eq ge _ _ _ _ _ (AB errB 0 4 ∗ (AB hb 0 14 ∗ K18D c c.m0)) _ _ (by acxD) ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (store_any ge _ _ _ _ _ _ _ .Mint32 errB _ 0 rfl rfl rfl
      (fun le m hT => lv_err (hT.get (by lm))) (fun le m hT => ⟨_, _, EvalExpr.Econst_int _ _, rfl⟩)) ?_
    refine heap_imp ge _ _ _ _ (AB errB 0 4 ∗ (AB hb 0 14 ∗ K18D c c.m0)) _ _ _
      (fun hp h => fin_heapDB c errB hb hp (by
        have e : AB errB 0 4 ∗ (AB hb 0 14 ∗ K18D c c.m0) = (AB hb 0 14 ∗ AB errB 0 4) ∗ K18D c c.m0 := by acxD
        rw [e] at h; exact h)) ?_
    exact retD ge _ _ hcenv errB hb _ _ _ _ _ _ _ (fun le m hT => by evx) (fun _ => by rfl)
      (fun hp h => h)
  · exact skip_to ge _ _ _ _ _ (fun e le hp ⟨he, hT, hH⟩ => ⟨n, hn, k, he, hT, hH⟩)

theorem s19DB (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env)  :
    Triple ge (FunctionEntry2 ge) FD0 (P19DB c errB hb) (sp 19 BD0)
      (RR (postDB c errB) Sep.Assn.no) := by
  unfD0
  refine lift_nDB ge _ _ _ (fun n hn => ?_)
  refine triple_lift ge _ _ (fun k => LocalSt (envD hb) ((_n, .Vlong k) :: L16D c errB n)
    ((AB hb 0 14 ∗ AB errB 0 4) ∗ K18D c c.m0)) _ _ _
    (fun e le hp h => h) (fun k => ?_)
  refine heap_imp ge _ _ _ _ _ _ _ _ (fun hp h => fin_heapDB c errB hb hp h) ?_
  exact retD ge _ _ hcenv errB hb _ _ _ (.Vlong k) (.Vlong k) _ _
    (fun le m hT => EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..))) (fun _ => rfl) (fun hp h => h)

end

/-! ## 本体と、関数の仕様（D0） -/

theorem body_dbefore (ge : CGenv) (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (c : Ctx)
    (X : ExtDB ge c.encB c.m0)
    (hpl : Integers.Int64.lt c.pl (Integers.Int64.repr 0) = false)
    (hrem : Integers.Int64.lt (Integers.Int64.repr 0) c.rem = false)
    (hdata : IsPtr c.dataV) (hout : IsPtr c.outV) (hm0 : c.m0.length = 4) (errB hb : Block) :
    Triple ge (FunctionEntry2 ge) FD0 (P0DB c errB hb) FD0.fn_body
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := postDB c errB } := by
  show Triple _ _ _ _ (sp 0 BD0) (RR (postDB c errB) Sep.Assn.no)
  refine chain ge _ _ BD0 0 _ _ _ _ rfl (s0DB ge c errB hb) ?_
  refine chain ge _ _ BD0 1 _ _ _ _ rfl (s1DB ge c errB hb hpl) ?_
  refine chain ge _ _ BD0 2 _ _ _ _ rfl (s2DB ge c errB hb hcenv hrem) ?_
  refine chain ge _ _ BD0 3 _ _ _ _ rfl (s3DB ge c errB hb hcenv X hdata) ?_
  refine chain ge _ _ BD0 4 _ _ _ _ rfl (s4DB ge c errB hb hcenv hm0) ?_
  refine chain ge _ _ BD0 5 _ _ _ _ rfl (s5DB ge c errB hb hcenv) ?_
  refine chain ge _ _ BD0 6 _ _ _ _ rfl (s6DB ge c errB hb hcenv X hdata hm0) ?_
  refine chain ge _ _ BD0 7 _ _ _ _ rfl (s7DB ge c errB hb hcenv X hdata hm0) ?_
  refine chain ge _ _ BD0 8 _ _ _ _ rfl (s8DB ge c errB hb hcenv X hdata hm0) ?_
  refine chain ge _ _ BD0 9 _ _ _ _ rfl (s9DB ge c errB hb hcenv) ?_
  refine chain ge _ _ BD0 10 _ _ _ _ rfl (s10DB ge c errB hb) ?_
  refine chain ge _ _ BD0 11 _ _ _ _ rfl (s11DB ge c errB hb hcenv) ?_
  refine chain ge _ _ BD0 12 _ _ _ _ rfl (s12DB ge c errB hb X hdata) ?_
  refine chain ge _ _ BD0 13 _ _ _ _ rfl (s13DB ge c errB hb hcenv X) ?_
  refine chain ge _ _ BD0 14 _ _ _ _ rfl (s14DB ge c errB hb) ?_
  refine chain ge _ _ BD0 15 _ _ _ _ rfl (s15DB ge c errB hb hcenv) ?_
  refine chain ge _ _ BD0 16 _ _ _ _ rfl (s16DB ge c errB hb X hout) ?_
  refine chain ge _ _ BD0 17 _ _ _ _ rfl (s17DB ge c errB hb hcenv) ?_
  refine chain ge _ _ BD0 18 _ _ _ _ rfl (s18DB ge c errB hb hcenv) ?_
  exact s19DB ge c errB hb hcenv

/-- 関数の仕様（D0）。前提は D1 と同じ。事後条件: `mask` は `m0` のまま。 -/
def specDB (c : Ctx) (errB : Block) : FunSpec where
  tyargs := [tptr easyT, tptr encT, tuint, tlong, tptr (Ty.Tstruct _bufq noattr), tptr tint]
  tyres := tlong
  cc := cc_default
  pre := fun vargs hp => vargs = [c.dataV, .Vptr c.encB Integers.Ptrofs.zero, .Vint c.fl, .Vlong c.pl, c.outV,
      .Vptr errB Integers.Ptrofs.zero]
    ∧ (encPre c ∗ AB errB 0 4) hp
  post := postDB c errB
  measure := fun _ => 0

theorem write_head_before_entry_wf :
    listNorepet (varNames FD0.fn_vars) ∧ listNorepet (varNames FD0.fn_params)
    ∧ listDisjoint (varNames FD0.fn_params) (varNames FD0.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **8.14.1（D0）の `ws_enc_write_head`**: U0 の `add_frame_before` と同じ形。`Curl_rand` を仮定せずに仕様を満たし、
    `Curl_bufq_write` に渡すヘッダの最後の4バイトは入口の `m0`（`bufqSpecD … c.m0 …` の前提）、戻ったあとも `enc->mask` は `m0`。 -/
theorem write_head_before (ge : CGenv) (hcenv : ge.genv_cenv = Deb2025_10148_deb_before.prog.prog_comp_env)
    (c : Ctx) (errB : Block) (X : ExtDB ge c.encB c.m0)
    (hpl : Integers.Int64.lt c.pl (Integers.Int64.repr 0) = false)
    (hrem : Integers.Int64.lt (Integers.Int64.repr 0) c.rem = false)
    (hdata : IsPtr c.dataV) (hout : IsPtr c.outV) (hm0 : c.m0.length = 4) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal FD0) (specDB c errB) vs := by
  have hcenv' := hcenv.trans cenv_deb_before_same
  by_cases hvs : vs = [c.dataV, .Vptr c.encB Integers.Ptrofs.zero, .Vint c.fl, .Vlong c.pl, c.outV,
      .Vptr errB Integers.Ptrofs.zero]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := write_head_before_entry_wf
  refine satisfies_internal ge (FunctionEntry2 ge) FD0 _ _
    (fun e le hp => ∃ hb, P0DB c errB hb e le hp)
    (fun m hp hf hpre hd hag => ?_)
    (triple_lift ge _ _ _ _ _ _ (fun e le hp h => h) (fun hb =>
      body_dbefore ge hcenv' c X hpl hrem hdata hout hm0 errB hb))
  let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv (tarray tuchar 14))
  have hav : AllocVariables ge.genv_cenv emptyEnv m FD0.fn_vars (envD a1.2) a1.1 :=
    .cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _)
  obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav hnv
    (by
      intro v hv
      simp only [FD0, Deb2025_10148_deb_before.f_ws_enc_write_head, List.mem_cons, List.mem_nil_iff,
        or_false] at hv
      subst hv; rw [hcenv]; decide)
    (Heap.union hp hf) hag
  have hL : Case3C.Locs [(a1.2, 14)] hl := by
    have := Case3C.locs_of_localsAt ge.genv_cenv _ _ hl hloc
    rw [hcenv] at this
    exact this
  simp only [Case3C.Locs, sep_emp_eq] at hL
  obtain ⟨dph, dfh⟩ := Heap.disjoint_union_left.mp hdl
  refine ⟨envD a1.2,
    PTree.set _err (.Vptr errB Integers.Ptrofs.zero) (PTree.set _out c.outV (PTree.set _payload_len (.Vlong c.pl)
      (PTree.set _flags (.Vint c.fl) (PTree.set _enc (.Vptr c.encB Integers.Ptrofs.zero) (PTree.set _data c.dataV
        (createUndefTemps FD0.fn_temps)))))),
    a1.1, hl, FunctionEntry2.intro hnv hnp hdisj hav rfl,
    Heap.disjoint_union_left.mpr ⟨hd, Heap.disjoint_comm dfh⟩, ?_, ?_⟩
  · rw [Heap.union_assoc, Heap.union_comm (Heap.disjoint_comm dfh), ← Heap.union_assoc]
    exact hagl
  · refine ⟨a1.2, rfl, ?_, ?_⟩
    · intro q hq
      simp only [LkD, Lk, List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · have : ((encPre c ∗ AB errB 0 4) ∗ AB a1.2 0 14) (Heap.union hp hl) := ⟨hp, hl, dph, rfl, hpre.2, hL⟩
      rw [sep_assoc_eq] at this
      exact this

/-! ## P0 の入力（D0）: 前提を満たす入口のメモリ

  U0 の `cE`・`mE` の構造体のブロックに加えて、`*err` のブロック（4バイト、`int` の 0）を割り当てる。
-/

def m1ED : Mem := (Mem.alloc Mem.empty 0 32).1
def bwED : Block := m1ED.nextblock
def m0ED : Mem := (Mem.alloc m1ED 0 4).1

def storesED : Option Mem := do
  let m ← Mem.store .Mint64 m0ED bwE 0 (.Vlong Integers.Int64.zero)
  let m ← Mem.store .Mint64 m bwE 8 (.Vlong Integers.Int64.zero)
  let m ← Mem.store .Mint32 m bwE 16 (.Vint Integers.Int.zero)
  let m ← Mem.store .Mint32 m bwE 20 (.Vint Integers.Int.zero)
  let m ← Mem.store .Mint32 m bwE 24 (.Vint Integers.Int.zero)
  Mem.store .Mint32 m bwED 0 (.Vint Integers.Int.zero)

theorem storesED_isSome : storesED.isSome = true := by decide

def mED : Mem := storesED.get storesED_isSome

theorem encPre_cED_satisfiable : ∃ hp, (encPre cE ∗ AB bwED 0 4) hp ∧ Heap.Agrees hp mED := by
  obtain ⟨h1, m1, g1⟩ := Case5C.cell (chunk := .Mint64) (b := bwE) (ofs := 0)
    (v := .Vlong Integers.Int64.zero) (m := mED) (by decide) (by decide)
  obtain ⟨h2, m2, g2⟩ := Case5C.cell (chunk := .Mint64) (b := bwE) (ofs := 8)
    (v := .Vlong Integers.Int64.zero) (m := mED) (by decide) (by decide)
  obtain ⟨h3, m3, g3⟩ := Case5C.cell (chunk := .Mint32) (b := bwE) (ofs := 16)
    (v := .Vint Integers.Int.zero) (m := mED) (by decide) (by decide)
  obtain ⟨h4, m4, g4⟩ := Case5C.cell (chunk := .Mint32) (b := bwE) (ofs := 20)
    (v := .Vint Integers.Int.zero) (m := mED) (by decide) (by decide)
  obtain ⟨h5, m5, g5⟩ := Case5C.cell (chunk := .Mint32) (b := bwE) (ofs := 24)
    (v := .Vint Integers.Int.zero) (m := mED) (by decide) (by decide)
  obtain ⟨h6, m6, g6⟩ := Case5C.cell (chunk := .Mint32) (b := bwED) (ofs := 0)
    (v := .Vint Integers.Int.zero) (m := mED) (by decide) (by decide)
  have hb : bwE ≠ bwED := by decide
  have dx : ∀ {h : Heap}, (∃ c o v, mapsto c .Freeable bwE o v h) → Heap.disjoint h h6 := by
    intro h ⟨c, o, v, hm⟩
    intro b' o'
    by_cases hbb : b' = bwE
    · subst hbb; exact Or.inr (mapsto_none m6 _ o' (Or.inl hb))
    · exact Or.inl (mapsto_none hm b' o' (Or.inl hbb))
  have d45 := Case5C.mapsto_disj m4 m5 (by decide)
  have d3 : Heap.disjoint h3 (Heap.union h4 h5) :=
    Heap.disjoint_union_right.mpr ⟨Case5C.mapsto_disj m3 m4 (by decide), Case5C.mapsto_disj m3 m5 (by decide)⟩
  have d2 : Heap.disjoint h2 (Heap.union h3 (Heap.union h4 h5)) :=
    Heap.disjoint_union_right.mpr ⟨Case5C.mapsto_disj m2 m3 (by decide),
      Heap.disjoint_union_right.mpr ⟨Case5C.mapsto_disj m2 m4 (by decide), Case5C.mapsto_disj m2 m5 (by decide)⟩⟩
  have d1 : Heap.disjoint h1 (Heap.union h2 (Heap.union h3 (Heap.union h4 h5))) :=
    Heap.disjoint_union_right.mpr ⟨Case5C.mapsto_disj m1 m2 (by decide),
      Heap.disjoint_union_right.mpr ⟨Case5C.mapsto_disj m1 m3 (by decide),
        Heap.disjoint_union_right.mpr ⟨Case5C.mapsto_disj m1 m4 (by decide), Case5C.mapsto_disj m1 m5 (by decide)⟩⟩⟩
  have d6 : Heap.disjoint (Heap.union h1 (Heap.union h2 (Heap.union h3 (Heap.union h4 h5)))) h6 :=
    Heap.disjoint_union_left.mpr ⟨dx ⟨_, _, _, m1⟩, Heap.disjoint_union_left.mpr ⟨dx ⟨_, _, _, m2⟩,
      Heap.disjoint_union_left.mpr ⟨dx ⟨_, _, _, m3⟩, Heap.disjoint_union_left.mpr ⟨dx ⟨_, _, _, m4⟩,
        dx ⟨_, _, _, m5⟩⟩⟩⟩⟩
  refine ⟨_, ⟨_, h6, d6, rfl, ⟨h1, _, d1, rfl, mapsto_anyB m1, h2, _, d2, rfl, m2, h3, _, d3, rfl,
    mapsto_anyB m3, h4, h5, d45, rfl, (pure_sep_elim m4).2, m5⟩, mapsto_anyB m6⟩,
    Case5C.agrees_union (Case5C.agrees_union g1 (Case5C.agrees_union g2 (Case5C.agrees_union g3
      (Case5C.agrees_union g4 g5)))) g6⟩

/-- **P0（C）、D0: 8.14.1 の関数は、送るヘッダの最後の4バイトに入口の `enc->mask`（`m0`）を使い、戻ったあとも `enc->mask` は `m0`。**
    前提を満たす入口のメモリがあることも示す（`cE`・`bwED`・`mED`）。 -/
theorem P0_C_debian :
    ∃ (c : Ctx) (errB : Block), (∃ hp m, (encPre c ∗ AB errB 0 4) hp ∧ Heap.Agrees hp m)
      ∧ Integers.Int64.lt c.pl (Integers.Int64.repr 0) = false
      ∧ Integers.Int64.lt (Integers.Int64.repr 0) c.rem = false
      ∧ IsPtr c.dataV ∧ IsPtr c.outV ∧ c.m0.length = 4
      ∧ ∀ ge : CGenv, ge.genv_cenv = Deb2025_10148_deb_before.prog.prog_comp_env → ExtDB ge c.encB c.m0 →
          ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal FD0) (specDB c errB) vs := by
  obtain ⟨hp, hH, hag⟩ := encPre_cED_satisfiable
  refine ⟨cE, bwED, ⟨hp, mED, hH, hag⟩, by decide, by decide, Or.inr ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩, rfl, ?_⟩
  intro ge hcenv X vs
  exact write_head_before ge hcenv cE bwED X (by decide) (by decide) (Or.inr ⟨_, rfl⟩) (Or.inr ⟨_, rfl⟩) rfl vs

end Deb2025_10148C
