/-
CVE-2025-10148: 上流の修正前（7c9878ff0c、84db7a9eae の親）の `ws_enc_add_frame`（U0）。

証明すること（`add_frame_before`、P0）: 修正前の関数は `Curl_rand` を呼ばない（外部関数の仮定 `ExtB` に `Curl_rand` が無い）。
`Curl_bufq_write` に渡すヘッダの最後の4バイトは入口の `enc->mask` の4バイト `m0` で（`bufqSpec … c.m0 …` の前提）、
戻ったあとも `enc->mask` は `m0` のまま（事後条件 `postB`）。`P0_C` は、前提を満たす入口のメモリが実際にあることも示す。

証明は U1（`Deb2025_10148After.lean`）の各文の証明を写し、一時変数の番号（clightgen の振り方が1つずれる）と、
`Curl_rand` の2文（U1 の 13・14 番目）を除いたことに合わせて直したもの。
-/
import Deb2025_10148After
import GenDeb2025_10148UpBefore
import Case5Witness
open CC CC.Sep CC.HProp
open Deb2025_10148_up_before
open Case5C (RR boolVal_ofBool_tint)
open Case4debC (IsPtr cast_ptr)
open Deb2026_3805C (call2 set2 call_none heap_eq heap_imp triple_lift temps_weak once_loop int_eq_false ex_map)

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Deb2025_10148C

theorem cenv_before_same : Deb2025_10148_up_before.prog.prog_comp_env
    = Deb2025_10148_up_after.prog.prog_comp_env := rfl

abbrev F0 : Function := Deb2025_10148_up_before.f_ws_enc_add_frame
abbrev B0 : Stmt := Deb2025_10148_up_before.f_ws_enc_add_frame.fn_body

macro "unfB" : tactic => `(tactic| (conv => arg 5; dsimp only [Deb2025_10148C.hdS, Deb2025_10148C.sp,
  Deb2025_10148C.B0, Deb2025_10148_up_before.f_ws_enc_add_frame]))

abbrev L4B (c : Ctx) (v : Val) : List (Ident × Val) :=
  (_result, v) :: (_t'1, v) :: (_t'11, cfV c) :: (_t'12, .Vlong c.rem) :: Lk c

/-- 事後条件（U0）: `*enc` の所有を返し、`mask` は入口の `m0` のまま。戻り値は問わない。 -/
def postB (c : Ctx) : Val → HProp := fun _ hp => encPost c.encB (mk0 c) hp

theorem post_B (c : Ctx) (wd : HProp) (hwd : ∀ h, wd h → AB c.encB 24 4 h)
    (v : Val) (hp : Heap) (h : encA c.encB (mk0 c) wd hp) : postB c v hp := by
  obtain ⟨h1, r1, d1, e1, a1, h2⟩ := h
  obtain ⟨h3, r3, d3, e3, a3, h4⟩ := h2
  obtain ⟨h5, r5, d5, e5, a5, h6⟩ := h4
  obtain ⟨h7, r7, d7, e7, a7, a8⟩ := h6
  exact ⟨h1, r1, d1, e1, a1, h3, r3, d3, e3, a3, h5, r5, d5, e5, a5, h7, r7, d7, e7, a7, hwd _ a8⟩

/-- 局所変数を手放して return する（U0）。 -/
theorem retUB (ge : CGenv) (fe) (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env)
    (fbB hb nwB : Block) (hne : fbB ≠ hb ∧ fbB ≠ nwB ∧ hb ≠ nwB)
    (l : List (Ident × Val)) (Hk : HProp) (a : Expr) (v : Val) (Ret : Val → HProp) (Q : Sep.Assn)
    (hev : ∀ le m, TempsHold l le → EvalExpr ge (envU fbB hb nwB) le m a v)
    (hcast : ∀ m, Cop.semCast v (typeof a) F0.fn_return m = some v)
    (hret : ∀ hp, Hk hp → Ret v hp) :
    Triple ge fe F0 (LocalSt (envU fbB hb nwB) l (Hk ∗ LU fbB hb nwB)) (.Sreturn (some a)) (RR Ret Q) := by
  rw [← locs_LU]
  refine triple_conseq ge fe F0
    (Case3C.ret_locs ge fe F0 (envU fbB hb nwB) l Hk [(fbB, 1), (hb, 14), (nwB, 8)] a v v Ret
      (fun le m _ hT _ _ => hev le m hT) hcast ?_ ?_ hret)
    (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
  · rw [blocks_envU ge hcenv]
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨hb, 14, rfl, by simp⟩
    · exact ⟨fbB, 1, rfl, by simp⟩
    · exact ⟨nwB, 8, rfl, by simp⟩
  · rw [blocks_envU ge hcenv]
    obtain ⟨h1, h2, h3⟩ := hne
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil))
    · intro y hy
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl
      · exact Ne.symm h1
      · exact h3
    · intro y hy
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      subst hy; exact h2
    · intro y hy; simp at hy

/-- 呼ばれる側の関数（U0）。`Curl_rand` は無い。`Curl_bufq_write` の前提の4バイトは `m0`。 -/
structure ExtB (ge : CGenv) (encB : Block) (m0 : List MemVal) : Prop where
  fail : ∃ b fd, Genv.findSymbol ge.genv_genv _Curl_failf = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr easyT, tptr tschar] tvoid ccVar
    ∧ ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fd failSpec vs
  fb : ∃ b fd, Genv.findSymbol ge.genv_genv _ws_frame_flags2firstbyte = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr easyT, tuint, tbool, tptr tuchar] tint cc_default
    ∧ ∀ fbB vs, SatisfiesAt ge (FunctionEntry2 ge) fd (fbSpec fbB) vs
  info : ∃ b fd, Genv.findSymbol ge.genv_genv _ws_enc_info = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr encT, tptr easyT, tptr tschar] tvoid cc_default
    ∧ ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fd infoSpec vs
  cpy : ∃ b fd, Genv.findSymbol ge.genv_genv _memcpy = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr tvoid, tptr tvoid, tulong] (tptr tvoid) cc_default
    ∧ ∀ hb n mb vs, SatisfiesAt ge (FunctionEntry2 ge) fd (cpySpec hb n encB mb) vs
  bufq : ∃ b fd, Genv.findSymbol ge.genv_genv _Curl_bufq_write = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr (Ty.Tstruct _bufq noattr), tptr tuchar, tulong, tptr tulong] tint cc_default
    ∧ ∀ hb n nwB vs, SatisfiesAt ge (FunctionEntry2 ge) fd (bufqSpec hb n m0 nwB) vs
  lit3 : ∃ b, Genv.findSymbol ge.genv_genv ___stringlit_3 = some b
  lit4 : ∃ b, Genv.findSymbol ge.genv_genv ___stringlit_4 = some b
  lit5 : ∃ b, Genv.findSymbol ge.genv_genv ___stringlit_5 = some b
  lit6 : ∃ b, Genv.findSymbol ge.genv_genv ___stringlit_6 = some b

section
variable (ge : CGenv) (c : Ctx) (fbB hb nwB : Block)

abbrev EUB := envU fbB hb nwB

def P0B : Sep.Assn := LocalSt (envU fbB hb nwB) (Lk c) (encPre c ∗ LU fbB hb nwB)

theorem s0B : Triple ge (FunctionEntry2 ge) F0 (P0B c fbB hb nwB) (hdS (sp 0 B0))
    (RR (postB c) (P0B c fbB hb nwB)) := by
  refine only_RR _ _ _ _ ?_
  show Sep.Triple _ _ _ _ (.Sassign (.Evar _firstb tuchar) (.Econst_int (Integers.Int.repr 0) tint)) _
  unfold P0B
  have he : encPre c ∗ LU fbB hb nwB = AB fbB 0 1 ∗ (encPre c ∗ AB hb 0 14 ∗ AB nwB 0 8) := by
    unfold LU; acx
  rw [he]
  exact store_any ge _ _ _ _ _ _ _ .Mint8unsigned fbB Integers.Ptrofs.zero 0 rfl rfl rfl
    (fun _ _ _ => eval_var_local (envU_fb _ _ _)) (fun _ _ _ => ⟨_, _, EvalExpr.Econst_int _ _, rfl⟩)

theorem s1B (hpl : Integers.Int64.lt c.pl (Integers.Int64.repr 0) = false) :
    Triple ge (FunctionEntry2 ge) F0 (P0B c fbB hb nwB) (hdS (sp 1 B0))
      (RR (postB c) (P0B c fbB hb nwB)) := by
  unfB
  unfold P0B
  refine if_val ge _ _ _ _ _ _ false _ _ _ (Val.ofBool false) ?_ (fun m => boolVal_ofBool_tint _ m) ?_
  · intro le m hp hT _ _
    refine EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm)))
      (EvalExpr.Econst_int _ _) ?_
    show some (Val.ofBool (Integers.Int64.lt c.pl (Integers.Int64.repr 0))) = _
    rw [hpl]
  · exact skip_to ge _ _ _ _ _ (fun _ _ _ x => x)

def P3B : Sep.Assn := LocalSt (envU fbB hb nwB) ((_t'12, .Vlong c.rem) :: Lk c)
  (encA c.encB (mk0 c) (wd32 c c.w) ∗ LU fbB hb nwB)

theorem s2B (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (hrem : Integers.Int64.lt (Integers.Int64.repr 0) c.rem = false) :
    Triple ge (FunctionEntry2 ge) F0 (P0B c fbB hb nwB) (hdS (sp 2 B0))
      (RR (postB c) (P3B c fbB hb nwB)) := by
  unfB
  unfold P0B
  have he : encPre c ∗ LU fbB hb nwB = mapsto .Mint64 .Freeable c.encB 8 (.Vlong c.rem)
      ∗ (AB c.encB 0 8 ∗ AB c.encB 16 4 ∗ mk0 c ∗ wd32 c c.w ∗ LU fbB hb nwB) := by
    unfold encPre; acx
  refine triple_seq_fwd ge _ _ _
    (LocalSt (envU fbB hb nwB) ((_t'12, .Vlong c.rem) :: Lk c) (encPre c ∗ LU fbB hb nwB)) _ _ _ ?_ ?_
  · refine set2 ge _ _ _ _ _ _t'12 _ (.Vlong c.rem) (by lf) ?_
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
      exact conv1 (P' := AB c.encB 8 8) (fun _ x => mapsto_anyB x) (by acx) hH


def P4B : Sep.Assn := fun e le hp => ∃ v,
  LocalSt (envU fbB hb nwB) (L4B c v) ((fbSpec fbB).post v ∗ K4 c hb nwB) e le hp

theorem s3B (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (X : ExtB ge c.encB c.m0) (hdata : IsPtr c.dataV) :
    Triple ge (FunctionEntry2 ge) F0 (P3B c fbB hb nwB) (hdS (sp 3 B0))
      (RR (postB c) (P4B c fbB hb nwB)) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.fb
  refine only_RR _ _ _ _ ?_
  unfB
  unfold P3B
  have hw : encA c.encB (mk0 c) (wd32 c c.w) ∗ LU fbB hb nwB = wd32 c c.w
      ∗ (AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ mk0 c ∗ LU fbB hb nwB) := by acx
  have hf : encA c.encB (mk0 c) (wd32 c c.w) ∗ LU fbB hb nwB = AB fbB 0 1 ∗ K4 c hb nwB := by
    acx
  refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ v, LocalSt (envU fbB hb nwB)
      ((_t'1, v) :: (_t'11, cfV c) :: (_t'12, .Vlong c.rem) :: Lk c)
      ((fbSpec fbB).post v ∗ K4 c hb nwB) e le hp) _ _ _ ?_ ?_
  · refine triple_seq_fwd ge _ _ _ (LocalSt (envU fbB hb nwB)
      ((_t'11, cfV c) :: (_t'12, .Vlong c.rem) :: Lk c)
      (encA c.encB (mk0 c) (wd32 c c.w) ∗ LU fbB hb nwB)) _ _ _ ?_ ?_
    · refine set2 ge _ _ _ _ _ _t'11 _ (cfV c) (by lf) ?_
      intro le m hp hT hH hag
      exact Case5C.eval_bitfield (hT.get (by lm)) (hcenv ▸ co_enc) (hcenv ▸ off_cf) (by decide)
        (by decide) (by show Mem.load .Mint32 m c.encB 24 = _; exact cell_ld hw hH hag)
    · rw [hf]
      refine call2 ge _ _ (fbSpec fbB) _t'1 _ _ _ _ (AB fbB 0 1) (K4 c hb nwB)
        [c.dataV, .Vint c.fl, boolOf (cfV c), .Vptr fbB Integers.Ptrofs.zero] bF fdF (hF fbB) hfF htF
        ?hcl (by lf) ?hc ?ha ?hp
      case hcl => rfl
      case hc => exact fun _ _ _ => eval_callee_global rfl hsF rfl
      case ha =>
        intro le m hT
        eargs
      case hp =>
        intro h hh
        exact ⟨⟨_, _, _, rfl⟩, hh⟩
  · refine ex_map ge _ _ _ _ _ (fun v => ?_)
    exact set2 ge _ _ _ _ _ _result _ v (by lf)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm)))

def P5B : Sep.Assn := fun e le hp => ∃ x, LocalSt (envU fbB hb nwB) (L4B c (.Vint Integers.Int.zero))
  (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K4 c hb nwB) e le hp

theorem s4B (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (hm0 : c.m0.length = 4) (hne : fbB ≠ hb ∧ fbB ≠ nwB ∧ hb ≠ nwB) :
    Triple ge (FunctionEntry2 ge) F0 (P4B c fbB hb nwB) (hdS (sp 4 B0))
      (RR (postB c) (P5B c fbB hb nwB)) := by
  unfB
  refine triple_lift ge _ _ (fun x : Val × Integers.Int => fun e le hp => x.1 = .Vint x.2
      ∧ LocalSt (envU fbB hb nwB) (L4B c x.1) ((fun hp => AB fbB 0 1 hp
        ∧ (x.2 = Integers.Int.zero → ∃ y, mapsto .Mint8unsigned .Freeable fbB 0 (.Vint y) hp))
        ∗ K4 c hb nwB) e le hp) _ _ _ ?_ (fun ⟨v, r⟩ => ?_)
  · intro e le hp ⟨v, he, hT, h1, h2, hd, heq, ⟨r, hv, ha, hx⟩, hk⟩
    exact ⟨(v, r), hv, he, hT, h1, h2, hd, heq, ⟨ha, hx⟩, hk⟩
  refine pure_l ge _ _ _ _ _ _ (fun hv => ?_)
  dsimp only at hv
  subst hv
  by_cases hr : r = Integers.Int.zero
  · subst hr
    refine if_val ge _ _ _ _ _ _ false _ _ _ (.Vint Integers.Int.zero)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (fun m => rfl) ?_
    exact skip_to ge _ _ _ _ _ (fun e le hp ⟨he, hT, h1, h2, hd, heq, ⟨_, hx⟩, hk⟩ =>
      let ⟨y, hm⟩ := hx rfl; ⟨y, he, hT, h1, h2, hd, heq, hm, hk⟩)
  · refine if_val ge _ _ _ _ _ _ true _ _ _ (.Vint r)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm)))
      (fun m => by show some (!Integers.Int.eq r Integers.Int.zero) = _; rw [int_eq_false hr]; rfl) ?_
    refine heap_imp ge _ _ _ _ _ (encA c.encB (mk0 c) (wd32 c c.w) ∗ LU fbB hb nwB) _ _
      (fun hp h => conv1 (P' := AB fbB 0 1) (fun _ x => x.1) (by acx) h) ?_
    exact retUB ge _ hcenv fbB hb nwB hne _ _ _ (.Vint r) _ _
      (fun le m hT => EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (fun _ => rfl)
      (fun hp h => post_B c _ (fun _ x => mapsto_anyB x) _ hp h)


def P6B : Sep.Assn := fun e le hp => ∃ x, LocalSt (envU fbB hb nwB) (L4B c (.Vint Integers.Int.zero))
  (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB) e le hp

theorem s5B (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) :
    Triple ge (FunctionEntry2 ge) F0 (P5B c fbB hb nwB) (hdS (sp 5 B0))
      (RR (postB c) (P6B c fbB hb nwB)) := by
  unfB
  refine triple_lift ge _ _ (fun x => LocalSt (envU fbB hb nwB) (L4B c (.Vint Integers.Int.zero))
    (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K4 c hb nwB)) _ _ _ (fun e le hp h => h) (fun x => ?_)
  have hk : mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K4 c hb nwB = wd32 c c.w
      ∗ (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ AB hb 0 14 ∗ AB nwB 0 8 ∗ AB c.encB 0 8
        ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ mk0 c) := by acx
  refine if_both ge _ _ _ _ _ _ _ _ _ (fun le m hT => ⟨_, _, by evx, rfl⟩) ?_ ?_
  · refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ n, LocalSt (envU fbB hb nwB)
      ((_t'2, .Vint n) :: L4B c (.Vint Integers.Int.zero))
      (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K4 c hb nwB) e le hp) _ _ _ ?_ ?_
    · refine if_both ge _ _ _ _ _ _ _ _ _ (fun le m hT => ⟨_, _, by evx, rfl⟩) ?_ ?_
      · exact triple_conseq ge _ _ (set2 ge _ _ _ _ _ _t'2 _ (.Vint Integers.Int.one) (by lf)
          (fun le m hp hT _ _ => by evx)) (fun _ _ _ x => x) (fun _ _ _ x => ⟨_, x⟩)
          (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
      · exact triple_conseq ge _ _ (set2 ge _ _ _ _ _ _t'2 _ (.Vint Integers.Int.zero) (by lf)
          (fun le m hp hT _ _ => by evx)) (fun _ _ _ x => x) (fun _ _ _ x => ⟨_, x⟩)
          (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
    · refine triple_lift ge _ _ (fun n => LocalSt (envU fbB hb nwB)
        ((_t'2, .Vint n) :: L4B c (.Vint Integers.Int.zero))
        (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K4 c hb nwB)) _ _ _ (fun e le hp h => h)
        (fun n => ?_)
      rw [hk]
      refine post_to ge _ _ _ (store_bit ge _ _ _ _ _ _ _ c.encB _ 24 8 c.w rfl (by decide) (by decide) rfl
        (fun le m hT => lv_enc hcenv (hT.get (by lm)) off_cf)
        (fun le m hT => ⟨_, _, EvalExpr.Etempvar _ _ _ (hT.get (by lm)), rfl⟩)) ?_
      intro e le hp ⟨c', he, hT, hH⟩
      exact ⟨x, he, TempsHold_mono (by ls) hT,
        conv1 (P' := AB c.encB 24 4) (fun _ y => mapsto_anyB y) (by acx) hH⟩
  · refine skip_to ge _ _ _ _ _ (fun e le hp ⟨he, hT, hH⟩ => ⟨x, he, hT, ?_⟩)
    rw [hk] at hH
    exact conv1 (P' := AB c.encB 24 4) (fun _ y => mapsto_anyB y) (by acx) hH

theorem s6B (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (X : ExtB ge c.encB c.m0)
    (hdata : IsPtr c.dataV) (hm0 : c.m0.length = 4) (hne : fbB ≠ hb ∧ fbB ≠ nwB ∧ hb ≠ nwB) :
    Triple ge (FunctionEntry2 ge) F0 (P6B c fbB hb nwB) (hdS (sp 6 B0))
      (RR (postB c) (P6B c fbB hb nwB)) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.fail
  obtain ⟨bL, hsL⟩ := X.lit3
  unfB
  refine triple_lift ge _ _ (fun x => LocalSt (envU fbB hb nwB) (L4B c (.Vint Integers.Int.zero))
    (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB)) _ _ _ (fun e le hp h => h) (fun x => ?_)
  refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ b : Bool, LocalSt (envU fbB hb nwB)
      ((_t'3, Val.ofBool b) :: L4B c (.Vint Integers.Int.zero))
      (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB) e le hp) _ _ _ ?_ ?_
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
  · refine triple_lift ge _ _ (fun b : Bool => LocalSt (envU fbB hb nwB)
      ((_t'3, Val.ofBool b) :: L4B c (.Vint Integers.Int.zero))
      (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB)) _ _ _ (fun e le hp h => h)
      (fun b => ?_)
    refine if_val ge _ _ _ _ _ _ b _ _ _ (Val.ofBool b)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (fun m => boolVal_ofBool_tint _ m) ?_
    cases b
    · exact skip_to ge _ _ _ _ _ (fun e le hp ⟨he, hT, hH⟩ => ⟨x, he, TempsHold_mono (by ls) hT, hH⟩)
    · refine heap_eq ge _ _ _ _ _ (emp ∗ (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB))
        _ _ (emp_l _) ?_
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (call_none ge _ _ failSpec _ _ _ _ emp _
        [c.dataV, .Vptr bL Integers.Ptrofs.zero] bF fdF hF hfF htF rfl
        (fun _ _ _ => eval_callee_global rfl hsF rfl) (fun le m hT => ?_) (fun _ h => h) (fun _ _ h => h)) ?_
      · refine EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (cast_ptr hdata _ _ _) ?_
        exact EvalExprlist.cons _ _ _ _ _ _ _ (eval_callee_global rfl hsL rfl) rfl EvalExprlist.nil
      · refine heap_imp ge _ _ _ _ _ (encA c.encB (mk0 c) (AB c.encB 24 4) ∗ LU fbB hb nwB) _ _
          (fun hp h => conv1 (P' := AB fbB 0 1) (fun _ y => mapsto_anyB y) (by acx) h) ?_
        exact retUB ge _ hcenv fbB hb nwB hne _ _ _ (.Vint (Integers.Int.repr 100)) _ _
          (fun le m hT => EvalExpr.Econst_int _ _) (fun _ => rfl)
          (fun hp h => post_B c _ (fun _ y => y) _ hp h)

theorem s7B (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (X : ExtB ge c.encB c.m0)
    (hdata : IsPtr c.dataV) (hm0 : c.m0.length = 4) (hne : fbB ≠ hb ∧ fbB ≠ nwB ∧ hb ≠ nwB) :
    Triple ge (FunctionEntry2 ge) F0 (P6B c fbB hb nwB) (hdS (sp 7 B0))
      (RR (postB c) (P6B c fbB hb nwB)) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.fail
  obtain ⟨bL, hsL⟩ := X.lit4
  unfB
  refine triple_lift ge _ _ (fun x => LocalSt (envU fbB hb nwB) (L4B c (.Vint Integers.Int.zero))
    (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB)) _ _ _ (fun e le hp h => h) (fun x => ?_)
  refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ b : Bool, LocalSt (envU fbB hb nwB)
      ((_t'4, Val.ofBool b) :: L4B c (.Vint Integers.Int.zero))
      (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB) e le hp) _ _ _ ?_ ?_
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
  · refine triple_lift ge _ _ (fun b : Bool => LocalSt (envU fbB hb nwB)
      ((_t'4, Val.ofBool b) :: L4B c (.Vint Integers.Int.zero))
      (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB)) _ _ _ (fun e le hp h => h)
      (fun b => ?_)
    refine if_val ge _ _ _ _ _ _ b _ _ _ (Val.ofBool b)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (fun m => boolVal_ofBool_tint _ m) ?_
    cases b
    · exact skip_to ge _ _ _ _ _ (fun e le hp ⟨he, hT, hH⟩ => ⟨x, he, TempsHold_mono (by ls) hT, hH⟩)
    · refine heap_eq ge _ _ _ _ _ (emp ∗ (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB))
        _ _ (emp_l _) ?_
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (call_none ge _ _ failSpec _ _ _ _ emp _
        [c.dataV, .Vptr bL Integers.Ptrofs.zero] bF fdF hF hfF htF rfl
        (fun _ _ _ => eval_callee_global rfl hsF rfl) (fun le m hT => ?_) (fun _ h => h) (fun _ _ h => h)) ?_
      · refine EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (cast_ptr hdata _ _ _) ?_
        exact EvalExprlist.cons _ _ _ _ _ _ _ (eval_callee_global rfl hsL rfl) rfl EvalExprlist.nil
      · refine heap_imp ge _ _ _ _ _ (encA c.encB (mk0 c) (AB c.encB 24 4) ∗ LU fbB hb nwB) _ _
          (fun hp h => conv1 (P' := AB fbB 0 1) (fun _ y => mapsto_anyB y) (by acx) h) ?_
        exact retUB ge _ hcenv fbB hb nwB hne _ _ _ (.Vint (Integers.Int.repr 100)) _ _
          (fun le m hT => EvalExpr.Econst_int _ _) (fun _ => rfl)
          (fun hp h => post_B c _ (fun _ y => y) _ hp h)

theorem s8B (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (X : ExtB ge c.encB c.m0)
    (hdata : IsPtr c.dataV) (hm0 : c.m0.length = 4) (hne : fbB ≠ hb ∧ fbB ≠ nwB ∧ hb ≠ nwB) :
    Triple ge (FunctionEntry2 ge) F0 (P6B c fbB hb nwB) (hdS (sp 8 B0))
      (RR (postB c) (P6B c fbB hb nwB)) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.fail
  obtain ⟨bL, hsL⟩ := X.lit5
  unfB
  refine triple_lift ge _ _ (fun x => LocalSt (envU fbB hb nwB) (L4B c (.Vint Integers.Int.zero))
    (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB)) _ _ _ (fun e le hp h => h) (fun x => ?_)
  refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ b : Bool, LocalSt (envU fbB hb nwB)
      ((_t'5, Val.ofBool b) :: L4B c (.Vint Integers.Int.zero))
      (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB) e le hp) _ _ _ ?_ ?_
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
  · refine triple_lift ge _ _ (fun b : Bool => LocalSt (envU fbB hb nwB)
      ((_t'5, Val.ofBool b) :: L4B c (.Vint Integers.Int.zero))
      (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB)) _ _ _ (fun e le hp h => h)
      (fun b => ?_)
    refine if_val ge _ _ _ _ _ _ b _ _ _ (Val.ofBool b)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (fun m => boolVal_ofBool_tint _ m) ?_
    cases b
    · exact skip_to ge _ _ _ _ _ (fun e le hp ⟨he, hT, hH⟩ => ⟨x, he, TempsHold_mono (by ls) hT, hH⟩)
    · refine heap_eq ge _ _ _ _ _ (emp ∗ (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB))
        _ _ (emp_l _) ?_
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (call_none ge _ _ failSpec _ _ _ _ emp _
        [c.dataV, .Vptr bL Integers.Ptrofs.zero] bF fdF hF hfF htF rfl
        (fun _ _ _ => eval_callee_global rfl hsF rfl) (fun le m hT => ?_) (fun _ h => h) (fun _ _ h => h)) ?_
      · refine EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (cast_ptr hdata _ _ _) ?_
        exact EvalExprlist.cons _ _ _ _ _ _ _ (eval_callee_global rfl hsL rfl) rfl EvalExprlist.nil
      · refine heap_imp ge _ _ _ _ _ (encA c.encB (mk0 c) (AB c.encB 24 4) ∗ LU fbB hb nwB) _ _
          (fun hp h => conv1 (P' := AB fbB 0 1) (fun _ y => mapsto_anyB y) (by acx) h) ?_
        exact retUB ge _ hcenv fbB hb nwB hne _ _ _ (.Vint (Integers.Int.repr 100)) _ _
          (fun le m hT => EvalExpr.Econst_int _ _) (fun _ => rfl)
          (fun hp h => post_B c _ (fun _ y => y) _ hp h)


def P10B : Sep.Assn := LocalSt (envU fbB hb nwB) (L4B c (.Vint Integers.Int.zero))
  (LU fbB hb nwB ∗ K10 c)

theorem s9B (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) :
    Triple ge (FunctionEntry2 ge) F0 (P6B c fbB hb nwB) (hdS (sp 9 B0))
      (RR (postB c) (P10B c fbB hb nwB)) := by
  unfB
  refine triple_lift ge _ _ (fun x => LocalSt (envU fbB hb nwB) (L4B c (.Vint Integers.Int.zero))
    (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB)) _ _ _ (fun e le hp h => h) (fun x => ?_)
  refine only_RR _ _ _ _ ?_
  have h24 : mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB
      = AB c.encB 24 4 ∗ (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ AB hb 0 14 ∗ AB nwB 0 8
        ∗ AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ mk0 c) := by acx
  have hh : AB c.encB 24 4 ∗ (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ AB hb 0 14 ∗ AB nwB 0 8
        ∗ AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ mk0 c)
      = AB hb 0 14 ∗ (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ AB nwB 0 8 ∗ K10 c) := by
    simp only [K10]; acx
  let L9 := (_t'6, Val.Vint (Integers.Int.zero_ext 8 (Integers.Int.zero_ext 8 x)))
    :: (_t'10, Val.Vint (Integers.Int.zero_ext 8 x)) :: L4B c (.Vint Integers.Int.zero)
  refine triple_seq_fwd ge _ _ _ (LocalSt (envU fbB hb nwB) L9
    (AB c.encB 24 4 ∗ (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ AB hb 0 14 ∗ AB nwB 0 8
        ∗ AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ mk0 c))) _ _ _ ?_ ?_
  · refine triple_seq_fwd ge _ _ _ (LocalSt (envU fbB hb nwB) L9
      (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB)) _ _ _ ?_ ?_
    · refine triple_seq_fwd ge _ _ _ (LocalSt (envU fbB hb nwB)
        ((_t'10, Val.Vint (Integers.Int.zero_ext 8 x)) :: L4B c (.Vint Integers.Int.zero))
        (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB)) _ _ _ ?_ ?_
      · refine set2 ge _ _ _ _ _ _t'10 _ _ (by lf) (fun le m hp hT hH hag => ?_)
        refine EvalExpr.Elvalue _ _ _ .Full _ (eval_var_local (envU_fb _ _ _)) (DerefLoc.value .Mint8unsigned _ rfl ?_)
        show Mem.load .Mint8unsigned m fbB 0 = _
        exact cell_ld rfl hH hag
      · exact set2 ge _ _ _ _ _ _t'6 _ _ (by lf) (fun le m hp hT _ _ =>
          EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) rfl)
    · rw [h24]
      exact store_byte ge _ _ _ _ _ _ _ c.encB _ 24 0 3 rfl rfl
        (fun le m hT => lv_enc hcenv (hT.get (by lm)) off_fb)
        (fun le m hT => ⟨_, _, EvalExpr.Etempvar _ _ _ (hT.get (by lm)), rfl⟩)
  · refine post_to ge _ _ _ (heap_eq ge _ _ _ _ _ _ _ _ hh
      (hstore ge _ _ _ _ _ hb (envU_head _ _ _) 0 13 rfl _ rfl
        (fun le m hT => ⟨_, _, EvalExpr.Etempvar _ _ _ (hT.get (by lm)), rfl⟩))) ?_
    intro e le hp ⟨he, hT, hH⟩
    refine ⟨he, TempsHold_mono (by ls) hT, ?_⟩
    have hq : AB hb 0 14 ∗ (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ AB nwB 0 8 ∗ K10 c)
        = mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ (AB hb 0 14 ∗ AB nwB 0 8 ∗ K10 c) := by acx
    rw [hq] at hH
    exact conv1 (P' := AB fbB 0 1) (fun _ y => mapsto_anyB (chunk := .Mint8unsigned) y) (by acx) hH

def P11B : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ LocalSt (envU fbB hb nwB) (L13 c n) (LU fbB hb nwB ∗ K10 c) e le hp

theorem s10B :
    Triple ge (FunctionEntry2 ge) F0 (P10B c fbB hb nwB) (hdS (sp 10 B0))
      (RR (postB c) (P11B c fbB hb nwB)) := by
  unfold P10B
  have hq : LU fbB hb nwB ∗ K10 c = AB hb 0 14 ∗ (AB fbB 0 1 ∗ AB nwB 0 8 ∗ K10 c) := by acx
  rw [hq]
  refine temps_weak ge _ _ _ _ ((_payload_len, .Vlong c.pl) :: L4B c (.Vint Integers.Int.zero)) _ _ _
    (by ls) ?_
  refine triple_conseq ge _ _ (hdr ge _ _ _ _ c.pl _ (postB c) hb (envU_head _ _ _) (by lf))
    (fun _ _ _ x => x) ?_ (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
  intro e le hp ⟨n, hn, he, hT, hH⟩
  exact ⟨n, hn, he, TempsHold_mono (by ls) hT, by rw [hq]; exact hH⟩

/-- `P11B` の `n` を取り出す。 -/
theorem lift_nB (P : Nat → Sep.Assn) (s : Stmt) (R : Sep.ExitConds)
    (h : ∀ n, (n = 2 ∨ n = 4 ∨ n = 10) → Triple ge (FunctionEntry2 ge) F0 (P n) s R) :
    Triple ge (FunctionEntry2 ge) F0 (fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10) ∧ P n e le hp) s R := by
  intro k e le hp hf m hd hag ⟨n, hn, hP⟩
  exact h n hn k e le hp hf m hd hag hP

theorem s11B (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) :
    Triple ge (FunctionEntry2 ge) F0 (P11B c fbB hb nwB) (hdS (sp 11 B0))
      (RR (postB c) (P11B c fbB hb nwB)) := by
  unfB
  refine lift_nB ge _ _ _ (fun n hn => ?_)
  have h0 : LU fbB hb nwB ∗ K10 c = AB c.encB 0 8 ∗ (AB fbB 0 1 ∗ AB hb 0 14 ∗ AB nwB 0 8 ∗ AB c.encB 8 8
      ∗ AB c.encB 16 4 ∗ mk0 c ∗ AB c.encB 24 4) := by acx
  have h8 : LU fbB hb nwB ∗ K10 c = AB c.encB 8 8 ∗ (AB fbB 0 1 ∗ AB hb 0 14 ∗ AB nwB 0 8 ∗ AB c.encB 0 8
      ∗ AB c.encB 16 4 ∗ mk0 c ∗ AB c.encB 24 4) := by acx
  let l7 := (_t'7, Val.Vlong c.pl) :: L13 c n
  refine post_to ge _ _ _ (P := LocalSt (envU fbB hb nwB) (L13 c n) (LU fbB hb nwB ∗ K10 c))
    (Q := LocalSt (envU fbB hb nwB) l7 (LU fbB hb nwB ∗ K10 c)) ?_
    (fun e le hp ⟨he, hT, hH⟩ => ⟨n, hn, he, TempsHold_mono (by ls) hT, hH⟩)
  refine triple_seq_fwd ge _ _ _ (LocalSt (envU fbB hb nwB) l7 (LU fbB hb nwB ∗ K10 c)) _ _ _ ?_ ?_
  · refine triple_seq_fwd ge _ _ _ (LocalSt (envU fbB hb nwB) l7 (LU fbB hb nwB ∗ K10 c)) _ _ _
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

theorem s12B (X : ExtB ge c.encB c.m0) (hdata : IsPtr c.dataV) :
    Triple ge (FunctionEntry2 ge) F0 (P11B c fbB hb nwB) (hdS (sp 12 B0))
      (RR (postB c) (P11B c fbB hb nwB)) := by
  obtain ⟨bI, fdI, hsI, hfI, htI, hI⟩ := X.info
  obtain ⟨bL, hsL⟩ := X.lit6
  unfB
  refine lift_nB ge _ _ _ (fun n hn => ?_)
  refine post_to ge _ _ _ (P := LocalSt (envU fbB hb nwB) (L13 c n) (LU fbB hb nwB ∗ K10 c))
    (Q := LocalSt (envU fbB hb nwB) (L13 c n) (LU fbB hb nwB ∗ K10 c)) ?_
    (fun e le hp h => ⟨n, hn, h⟩)
  refine heap_eq ge _ _ _ _ _ (emp ∗ (LU fbB hb nwB ∗ K10 c)) _ _ (emp_l _) ?_
  refine call_none ge _ _ infoSpec _ _ _ _ emp _
    [.Vptr c.encB Integers.Ptrofs.zero, c.dataV, .Vptr bL Integers.Ptrofs.zero] bI fdI hI hfI htI rfl
    (fun _ _ _ => eval_callee_global rfl hsI rfl) (fun le m hT => ?_) (fun _ h => h) (fun _ _ h => h)
  exact EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) rfl
    (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (cast_ptr hdata _ _ _)
    (EvalExprlist.cons _ _ _ _ _ _ _ (eval_callee_global rfl hsL rfl) rfl EvalExprlist.nil))


def P15B : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ ∃ v, LocalSt (envU fbB hb nwB) (L13 c n)
    ((cpySpec hb n c.encB c.m0).post v ∗ K15 c fbB hb nwB n) e le hp

theorem s13B (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (X : ExtB ge c.encB c.m0) :
    Triple ge (FunctionEntry2 ge) F0 (P11B c fbB hb nwB) (hdS (sp 13 B0))
      (RR (postB c) (P15B c fbB hb nwB)) := by
  obtain ⟨bC, fdC, hsC, hfC, htC, hC⟩ := X.cpy
  unfB
  refine lift_nB ge _ _ _ (fun n hn => ?_)
  refine post_to ge _ _ _ (Q := fun e le hp => ∃ v, LocalSt (envU fbB hb nwB) (L13 c n)
    ((cpySpec hb n c.encB c.m0).post v ∗ K15 c fbB hb nwB n) e le hp) ?_ (fun e le hp h => ⟨n, hn, h⟩)
  have hq : LU fbB hb nwB ∗ K10 c
      = (AB hb n 4 ∗ bytesPtsTo c.encB .Freeable 20 c.m0) ∗ K15 c fbB hb nwB n := by
    simp only [K10, LU]; rw [head_split hb n (hn_le hn)]; acx
  rw [hq]
  refine call_none_ex ge _ _ (cpySpec hb n c.encB c.m0) _ _ _ _ _ _ bC fdC (hC hb n c.m0) hfC htC rfl
    (fun _ _ _ => eval_callee_global rfl hsC rfl) (fun le m hT => ?_)
  have hl : (_hlen, Val.Vlong (Integers.Int64.repr n)) ∈ L13 c n := List.mem_cons_self ..
  rcases hn with rfl | rfl | rfl <;>
  · refine ⟨_, EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Elvalue _ _ _ _ _ (eval_var_local (envU_head _ _ _)) (DerefLoc.reference rfl))
        (EvalExpr.Etempvar _ _ _ (hT.get hl)) rfl) rfl
      (EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Eaddrof _ _ _ _ (lv_enc hcenv (hT.get (by lm)) off_mask)) rfl
      (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl EvalExprlist.nil)), ?_⟩
    exact fun h hh => ⟨⟨_, _, rfl, rfl, rfl⟩, hh⟩

def P16B : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ LocalSt (envU fbB hb nwB) (L16 c n)
    ((bytesPtsTo hb .Freeable n c.m0 ∗ bytesPtsTo c.encB .Freeable 20 c.m0) ∗ K15 c fbB hb nwB n) e le hp

theorem s14B :
    Triple ge (FunctionEntry2 ge) F0 (P15B c fbB hb nwB) (hdS (sp 14 B0))
      (RR (postB c) (P16B c fbB hb nwB)) := by
  unfB
  refine lift_nB ge _ _ _ (fun n hn => ?_)
  refine triple_lift ge _ _ (fun v => LocalSt (envU fbB hb nwB) (L13 c n)
    ((cpySpec hb n c.encB c.m0).post v ∗ K15 c fbB hb nwB n)) _ _ _ (fun e le hp h => h) (fun v => ?_)
  refine post_to ge _ _ _ (triple_set_local ge _ _ _ (L13 c n) (Lk c) _ _hlen _
    (.Vlong (Integers.Int64.repr ((n : Z) + 4))) (by ls) (by lf) (fun le m hp hT _ _ => ?_)) ?_
  · refine EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..)))
      (EvalExpr.Econst_int _ _) ?_
    rcases hn with rfl | rfl | rfl <;> rfl
  · exact fun e le hp h => ⟨n, hn, h⟩

theorem s15B (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) :
    Triple ge (FunctionEntry2 ge) F0 (P16B c fbB hb nwB) (hdS (sp 15 B0))
      (RR (postB c) (P16B c fbB hb nwB)) := by
  unfB
  refine lift_nB ge _ _ _ (fun n hn => ?_)
  refine post_to ge _ _ _ ?_ (fun e le hp h => ⟨n, hn, h⟩)
  have hq : (bytesPtsTo hb .Freeable n c.m0 ∗ bytesPtsTo c.encB .Freeable 20 c.m0) ∗ K15 c fbB hb nwB n
      = AB c.encB 16 4 ∗ (bytesPtsTo hb .Freeable n c.m0 ∗ bytesPtsTo c.encB .Freeable 20 c.m0 ∗ AB hb 0 n
        ∗ AB hb ((n : Z) + 4) (10 - n) ∗ AB fbB 0 1 ∗ AB nwB 0 8 ∗ AB c.encB 0 8 ∗ AB c.encB 8 8
        ∗ AB c.encB 24 4) := by acx
  rw [hq]
  exact store_any ge _ _ _ _ _ _ _ .Mint32 c.encB _ 16 rfl rfl rfl
    (fun le m hT => lv_enc hcenv (hT.get (by lm)) off_xori)
    (fun le m hT => ⟨_, _, EvalExpr.Econst_int _ _, rfl⟩)

def P18B : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ ∃ v, LocalSt (envU fbB hb nwB) ((_result, v) :: (_t'8, v) :: L16 c n)
    ((bufqSpec hb n c.m0 nwB).post v ∗ K18 c fbB c.m0) e le hp

theorem s16B (X : ExtB ge c.encB c.m0) (hout : IsPtr c.outV) :
    Triple ge (FunctionEntry2 ge) F0 (P16B c fbB hb nwB) (hdS (sp 16 B0))
      (RR (postB c) (P18B c fbB hb nwB)) := by
  obtain ⟨bQ, fdQ, hsQ, hfQ, htQ, hQ⟩ := X.bufq
  unfB
  refine lift_nB ge _ _ _ (fun n hn => ?_)
  refine post_to ge _ _ _ (Q := fun e le hp => ∃ v, LocalSt (envU fbB hb nwB) ((_result, v) :: (_t'8, v) :: L16 c n)
    ((bufqSpec hb n c.m0 nwB).post v ∗ K18 c fbB c.m0) e le hp) ?_ (fun e le hp h => ⟨n, hn, h⟩)
  have hq : (bytesPtsTo hb .Freeable n c.m0 ∗ bytesPtsTo c.encB .Freeable 20 c.m0) ∗ K15 c fbB hb nwB n
      = (AB hb 0 n ∗ bytesPtsTo hb .Freeable n c.m0 ∗ AB hb ((n : Z) + 4) (10 - n) ∗ AB nwB 0 8)
        ∗ K18 c fbB c.m0 := by acx
  rw [hq]
  refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ v, LocalSt (envU fbB hb nwB) ((_t'8, v) :: L16 c n)
    ((bufqSpec hb n c.m0 nwB).post v ∗ K18 c fbB c.m0) e le hp) _ _ _ ?_ ?_
  · refine call2 ge _ _ (bufqSpec hb n c.m0 nwB) _t'8 _ _ _ _ _ (K18 c fbB c.m0)
      [c.outV, .Vptr hb Integers.Ptrofs.zero, .Vlong (Integers.Int64.repr ((n : Z) + 4)),
        .Vptr nwB Integers.Ptrofs.zero] bQ fdQ (hQ hb n nwB) hfQ htQ ?hcl (by lf) ?hc ?ha ?hp
    case hcl => rfl
    case hc => exact fun _ _ _ => eval_callee_global rfl hsQ rfl
    case ha =>
      intro le m hT
      exact EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (cast_ptr hout _ _ _)
        (EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Elvalue _ _ _ _ _ (eval_var_local (envU_head _ _ _)) (DerefLoc.reference rfl)) rfl
        (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..))) rfl
        (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Eaddrof _ _ _ _ (eval_var_local (envU_nw _ _ _))) rfl
          EvalExprlist.nil)))
    case hp => exact fun h hh => ⟨⟨c.outV, rfl⟩, hh⟩
  · refine ex_map ge _ _ _ _ _ (fun v => ?_)
    exact set2 ge _ _ _ _ _ _result _ v (by lf)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm)))

/-- 出口: `nwritten` を手放す（`mask` は入口の `m0` のまま）。 -/
theorem fin_heapB (k : Integers.Int64) (hp : Heap)
    (h : (mapsto .Mint64 .Freeable nwB 0 (.Vlong k) ∗ (AB hb 0 14 ∗ K18 c fbB c.m0)) hp) :
    (encPost c.encB (mk0 c) ∗ LU fbB hb nwB) hp := by
  have h1 := sep_imp_l (P' := AB nwB 0 8) (fun _ y => mapsto_anyB (chunk := .Mint64) y) h
  have e1 : AB nwB 0 8 ∗ (AB hb 0 14 ∗ K18 c fbB c.m0) = encPost c.encB (mk0 c) ∗ LU fbB hb nwB := by acx
  rw [e1] at h1
  exact h1

def P19B : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ ∃ k, LocalSt (envU fbB hb nwB) (L16 c n)
    (mapsto .Mint64 .Freeable nwB 0 (.Vlong k) ∗ (AB hb 0 14 ∗ K18 c fbB c.m0)) e le hp

theorem s17B (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env)
    (hne : fbB ≠ hb ∧ fbB ≠ nwB ∧ hb ≠ nwB) :
    Triple ge (FunctionEntry2 ge) F0 (P18B c fbB hb nwB) (hdS (sp 17 B0))
      (RR (postB c) (P19B c fbB hb nwB)) := by
  unfB
  refine lift_nB ge _ _ _ (fun n hn => ?_)
  refine triple_lift ge _ _ (fun x : Val × Integers.Int × Integers.Int64 => fun e le hp => x.1 = .Vint x.2.1
      ∧ LocalSt (envU fbB hb nwB) ((_result, x.1) :: (_t'8, x.1) :: L16 c n)
        (mapsto .Mint64 .Freeable nwB 0 (.Vlong x.2.2) ∗ (AB hb 0 14 ∗ K18 c fbB c.m0)) e le hp) _ _ _ ?_
      (fun ⟨v, r, k⟩ => ?_)
  · intro e le hp ⟨v, he, hT, h1, h2, hd, heq, ⟨r, k, hv, hh⟩, hk⟩
    refine ⟨(v, r, k), hv, he, hT, ?_⟩
    have e1 : (AB hb 0 14 ∗ mapsto .Mint64 .Freeable nwB 0 (.Vlong k)) ∗ K18 c fbB c.m0
        = mapsto .Mint64 .Freeable nwB 0 (.Vlong k) ∗ (AB hb 0 14 ∗ K18 c fbB c.m0) := by acx
    rw [← e1]
    exact ⟨h1, h2, hd, heq, hh, hk⟩
  refine pure_l ge _ _ _ _ _ _ (fun hv => ?_)
  dsimp only at hv
  subst hv
  by_cases hr : r = Integers.Int.zero
  · subst hr
    refine if_val ge _ _ _ _ _ _ false _ _ _ (.Vint Integers.Int.zero)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (fun m => rfl) ?_
    exact skip_to ge _ _ _ _ _ (fun e le hp ⟨he, hT, hH⟩ => ⟨n, hn, k, he, TempsHold_mono (by ls) hT, hH⟩)
  · refine if_val ge _ _ _ _ _ _ true _ _ _ (.Vint r)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm)))
      (fun m => by show some (!Integers.Int.eq r Integers.Int.zero) = _; rw [int_eq_false hr]; rfl) ?_
    refine heap_imp ge _ _ _ _ _ _ _ _ (fun hp h => fin_heapB c fbB hb nwB k hp h) ?_
    exact retUB ge _ hcenv fbB hb nwB hne _ _ _ (.Vint r) _ _
      (fun le m hT => EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (fun _ => rfl) (fun hp h => h)

theorem s18B (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env)
    (hne : fbB ≠ hb ∧ fbB ≠ nwB ∧ hb ≠ nwB) :
    Triple ge (FunctionEntry2 ge) F0 (P19B c fbB hb nwB) (hdS (sp 18 B0))
      (RR (postB c) (P19B c fbB hb nwB)) := by
  unfB
  refine lift_nB ge _ _ _ (fun n hn => ?_)
  refine triple_lift ge _ _ (fun k => LocalSt (envU fbB hb nwB) (L16 c n)
    (mapsto .Mint64 .Freeable nwB 0 (.Vlong k) ∗ (AB hb 0 14 ∗ K18 c fbB c.m0))) _ _ _
    (fun e le hp h => h) (fun k => ?_)
  refine triple_seq_fwd ge _ _ _ (LocalSt (envU fbB hb nwB) ((_t'9, .Vlong k) :: L16 c n)
    (mapsto .Mint64 .Freeable nwB 0 (.Vlong k) ∗ (AB hb 0 14 ∗ K18 c fbB c.m0))) _ _ _ ?_ ?_
  · refine set2 ge _ _ _ _ _ _t'9 _ _ (by lf) (fun le m hp hT hH hag => ?_)
    refine EvalExpr.Elvalue _ _ _ .Full _ (eval_var_local (envU_nw _ _ _)) (DerefLoc.value .Mint64 _ rfl ?_)
    show Mem.load .Mint64 m nwB 0 = _
    exact cell_ld rfl hH hag
  · refine if_both ge _ _ _ _ _ _ _ _ _ (fun le m hT =>
      ⟨Val.ofBool (!Integers.Int64.eq k (Integers.Int64.repr ((n : Z) + 4))), _,
        EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..)))
          (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) rfl, boolVal_ofBool_tint _ _⟩) ?_ ?_
    · refine triple_seq_fwd ge _ _ _ _ _ _ _ (once_loop ge _ _ _ _ _ (triple_skip ge _ _ _)) ?_
      refine heap_imp ge _ _ _ _ _ _ _ _ (fun hp h => fin_heapB c fbB hb nwB k hp h) ?_
      exact retUB ge _ hcenv fbB hb nwB hne _ _ _ (.Vint (Integers.Int.repr 55)) _ _
        (fun le m hT => EvalExpr.Econst_int _ _) (fun _ => rfl) (fun hp h => h)
    · exact skip_to ge _ _ _ _ _ (fun e le hp ⟨he, hT, hH⟩ => ⟨n, hn, k, he, TempsHold_mono (by ls) hT, hH⟩)

theorem s19B (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env)
    (hne : fbB ≠ hb ∧ fbB ≠ nwB ∧ hb ≠ nwB) :
    Triple ge (FunctionEntry2 ge) F0 (P19B c fbB hb nwB) (sp 19 B0)
      (RR (postB c) Sep.Assn.no) := by
  unfB
  refine lift_nB ge _ _ _ (fun n hn => ?_)
  refine triple_lift ge _ _ (fun k => LocalSt (envU fbB hb nwB) (L16 c n)
    (mapsto .Mint64 .Freeable nwB 0 (.Vlong k) ∗ (AB hb 0 14 ∗ K18 c fbB c.m0))) _ _ _
    (fun e le hp h => h) (fun k => ?_)
  refine heap_imp ge _ _ _ _ _ _ _ _ (fun hp h => fin_heapB c fbB hb nwB k hp h) ?_
  exact retUB ge _ hcenv fbB hb nwB hne _ _ _ (.Vint Integers.Int.zero) _ _
    (fun le m hT => EvalExpr.Econst_int _ _) (fun _ => rfl) (fun hp h => h)

end

/-! ## 本体と、関数の仕様（U0） -/

theorem body_before (ge : CGenv) (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (c : Ctx)
    (X : ExtB ge c.encB c.m0)
    (hpl : Integers.Int64.lt c.pl (Integers.Int64.repr 0) = false)
    (hrem : Integers.Int64.lt (Integers.Int64.repr 0) c.rem = false)
    (hdata : IsPtr c.dataV) (hout : IsPtr c.outV) (hm0 : c.m0.length = 4)
    (fbB hb nwB : Block) (hne : fbB ≠ hb ∧ fbB ≠ nwB ∧ hb ≠ nwB) :
    Triple ge (FunctionEntry2 ge) F0 (P0B c fbB hb nwB) F0.fn_body
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := postB c } := by
  show Triple _ _ _ _ (sp 0 B0) (RR (postB c) Sep.Assn.no)
  refine chain ge _ _ B0 0 _ _ _ _ rfl (s0B ge c fbB hb nwB) ?_
  refine chain ge _ _ B0 1 _ _ _ _ rfl (s1B ge c fbB hb nwB hpl) ?_
  refine chain ge _ _ B0 2 _ _ _ _ rfl (s2B ge c fbB hb nwB hcenv hrem) ?_
  refine chain ge _ _ B0 3 _ _ _ _ rfl (s3B ge c fbB hb nwB hcenv X hdata) ?_
  refine chain ge _ _ B0 4 _ _ _ _ rfl (s4B ge c fbB hb nwB hcenv hm0 hne) ?_
  refine chain ge _ _ B0 5 _ _ _ _ rfl (s5B ge c fbB hb nwB hcenv) ?_
  refine chain ge _ _ B0 6 _ _ _ _ rfl (s6B ge c fbB hb nwB hcenv X hdata hm0 hne) ?_
  refine chain ge _ _ B0 7 _ _ _ _ rfl (s7B ge c fbB hb nwB hcenv X hdata hm0 hne) ?_
  refine chain ge _ _ B0 8 _ _ _ _ rfl (s8B ge c fbB hb nwB hcenv X hdata hm0 hne) ?_
  refine chain ge _ _ B0 9 _ _ _ _ rfl (s9B ge c fbB hb nwB hcenv) ?_
  refine chain ge _ _ B0 10 _ _ _ _ rfl (s10B ge c fbB hb nwB) ?_
  refine chain ge _ _ B0 11 _ _ _ _ rfl (s11B ge c fbB hb nwB hcenv) ?_
  refine chain ge _ _ B0 12 _ _ _ _ rfl (s12B ge c fbB hb nwB X hdata) ?_
  refine chain ge _ _ B0 13 _ _ _ _ rfl (s13B ge c fbB hb nwB hcenv X) ?_
  refine chain ge _ _ B0 14 _ _ _ _ rfl (s14B ge c fbB hb nwB) ?_
  refine chain ge _ _ B0 15 _ _ _ _ rfl (s15B ge c fbB hb nwB hcenv) ?_
  refine chain ge _ _ B0 16 _ _ _ _ rfl (s16B ge c fbB hb nwB X hout) ?_
  refine chain ge _ _ B0 17 _ _ _ _ rfl (s17B ge c fbB hb nwB hcenv hne) ?_
  refine chain ge _ _ B0 18 _ _ _ _ rfl (s18B ge c fbB hb nwB hcenv hne) ?_
  exact s19B ge c fbB hb nwB hcenv hne

/-- 関数の仕様（U0）。前提は U1 と同じ。事後条件: `*enc` の所有を返し、`mask` は `m0` のまま。 -/
def specB (c : Ctx) : FunSpec where
  tyargs := [tptr easyT, tptr encT, tuint, tlong, tptr (Ty.Tstruct _bufq noattr)]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [c.dataV, .Vptr c.encB Integers.Ptrofs.zero, .Vint c.fl, .Vlong c.pl, c.outV]
    ∧ encPre c hp
  post := postB c
  measure := fun _ => 0

theorem add_frame_before_entry_wf :
    listNorepet (varNames F0.fn_vars) ∧ listNorepet (varNames F0.fn_params)
    ∧ listDisjoint (varNames F0.fn_params) (varNames F0.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **修正前の `ws_enc_add_frame`（U0）**: `Curl_rand` を仮定せずに仕様を満たす。`Curl_bufq_write` に渡すヘッダの最後の4バイトは
    入口の `enc->mask`（`m0`、`bufqSpec … c.m0 …` の前提）で、戻ったあとも `enc->mask` は `m0`（`postB`）。 -/
theorem add_frame_before (ge : CGenv) (hcenv : ge.genv_cenv = Deb2025_10148_up_before.prog.prog_comp_env)
    (c : Ctx) (X : ExtB ge c.encB c.m0)
    (hpl : Integers.Int64.lt c.pl (Integers.Int64.repr 0) = false)
    (hrem : Integers.Int64.lt (Integers.Int64.repr 0) c.rem = false)
    (hdata : IsPtr c.dataV) (hout : IsPtr c.outV) (hm0 : c.m0.length = 4) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal F0) (specB c) vs := by
  have hcenv' := hcenv.trans cenv_before_same
  by_cases hvs : vs = [c.dataV, .Vptr c.encB Integers.Ptrofs.zero, .Vint c.fl, .Vlong c.pl, c.outV]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := add_frame_before_entry_wf
  refine satisfies_internal ge (FunctionEntry2 ge) F0 _ _
    (fun e le hp => ∃ x : Block × Block × Block, (x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧ x.2.1 ≠ x.2.2)
      ∧ P0B c x.1 x.2.1 x.2.2 e le hp)
    (fun m hp hf hpre hd hag => ?_)
    (triple_lift ge _ _ _ _ _ _ (fun e le hp h => h) (fun x => pure_l ge _ _ _ _ _ _ (fun hne =>
      body_before ge hcenv' c X hpl hrem hdata hout hm0 x.1 x.2.1 x.2.2 hne)))
  let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv tuchar)
  let a2 := Mem.alloc a1.1 0 (sizeof ge.genv_cenv (tarray tuchar 14))
  let a3 := Mem.alloc a2.1 0 (sizeof ge.genv_cenv tulong)
  have hav : AllocVariables ge.genv_cenv emptyEnv m F0.fn_vars (envU a1.2 a2.2 a3.2) a3.1 :=
    .cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _)))
  obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav hnv
    (by
      intro v hv
      simp only [F0, Deb2025_10148_up_before.f_ws_enc_add_frame, List.mem_cons, List.mem_nil_iff,
        or_false] at hv
      rcases hv with rfl | rfl | rfl <;> (rw [hcenv]; decide))
    (Heap.union hp hf) hag
  have hL : Case3C.Locs [(a1.2, 1), (a2.2, 14), (a3.2, 8)] hl := by
    have := Case3C.locs_of_localsAt ge.genv_cenv _ _ hl hloc
    rw [hcenv] at this
    exact this
  have hne := Case3C.locs3_ne hL (by decide) (by decide) (by decide)
  rw [locs_LU] at hL
  obtain ⟨dph, dfh⟩ := Heap.disjoint_union_left.mp hdl
  refine ⟨envU a1.2 a2.2 a3.2,
    PTree.set _out c.outV (PTree.set _payload_len (.Vlong c.pl) (PTree.set _flags (.Vint c.fl)
      (PTree.set _enc (.Vptr c.encB Integers.Ptrofs.zero) (PTree.set _data c.dataV
        (createUndefTemps F0.fn_temps))))),
    a3.1, hl, FunctionEntry2.intro hnv hnp hdisj hav rfl,
    Heap.disjoint_union_left.mpr ⟨hd, Heap.disjoint_comm dfh⟩, ?_, ?_⟩
  · rw [Heap.union_assoc, Heap.union_comm (Heap.disjoint_comm dfh), ← Heap.union_assoc]
    exact hagl
  · refine ⟨(a1.2, a2.2, a3.2), hne, rfl, ?_, ⟨hp, hl, dph, rfl, hpre.2, hL⟩⟩
    intro q hq
    simp only [Lk, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> rfl


/-! ## P0 の入力: 前提を満たす入口のメモリ

  1つのブロック（32 バイト）: 0 と 8 に `long` の 0、16・20・24 に `int` の 0。`enc->mask`（20〜23）の4バイト `m0` は
  `int` の 0 を符号化したもの。`payload_len` は 0、`payload_remain` は 0。
-/

def bwE : Block := Mem.empty.nextblock
def m0E : Mem := (Mem.alloc Mem.empty 0 32).1

def storesE : Option Mem := do
  let m ← Mem.store .Mint64 m0E bwE 0 (.Vlong Integers.Int64.zero)
  let m ← Mem.store .Mint64 m bwE 8 (.Vlong Integers.Int64.zero)
  let m ← Mem.store .Mint32 m bwE 16 (.Vint Integers.Int.zero)
  let m ← Mem.store .Mint32 m bwE 20 (.Vint Integers.Int.zero)
  Mem.store .Mint32 m bwE 24 (.Vint Integers.Int.zero)

theorem storesE_isSome : storesE.isSome = true := by decide

def mE : Mem := storesE.get storesE_isSome

def cE : Ctx where
  dataV := .Vlong Integers.Int64.zero
  encB := bwE
  fl := Integers.Int.zero
  pl := Integers.Int64.zero
  outV := .Vlong Integers.Int64.zero
  rem := Integers.Int64.zero
  w := Integers.Int.zero
  m0 := encodeVal .Mint32 (.Vint Integers.Int.zero)

theorem encPre_cE_satisfiable : ∃ hp, encPre cE hp ∧ Heap.Agrees hp mE := by
  obtain ⟨h1, m1, g1⟩ := Case5C.cell (chunk := .Mint64) (b := bwE) (ofs := 0)
    (v := .Vlong Integers.Int64.zero) (m := mE) (by decide) (by decide)
  obtain ⟨h2, m2, g2⟩ := Case5C.cell (chunk := .Mint64) (b := bwE) (ofs := 8)
    (v := .Vlong Integers.Int64.zero) (m := mE) (by decide) (by decide)
  obtain ⟨h3, m3, g3⟩ := Case5C.cell (chunk := .Mint32) (b := bwE) (ofs := 16)
    (v := .Vint Integers.Int.zero) (m := mE) (by decide) (by decide)
  obtain ⟨h4, m4, g4⟩ := Case5C.cell (chunk := .Mint32) (b := bwE) (ofs := 20)
    (v := .Vint Integers.Int.zero) (m := mE) (by decide) (by decide)
  obtain ⟨h5, m5, g5⟩ := Case5C.cell (chunk := .Mint32) (b := bwE) (ofs := 24)
    (v := .Vint Integers.Int.zero) (m := mE) (by decide) (by decide)
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
  refine ⟨_, ⟨h1, _, d1, rfl, mapsto_anyB m1, h2, _, d2, rfl, m2, h3, _, d3, rfl, mapsto_anyB m3,
    h4, h5, d45, rfl, (pure_sep_elim m4).2, m5⟩,
    Case5C.agrees_union g1 (Case5C.agrees_union g2 (Case5C.agrees_union g3 (Case5C.agrees_union g4 g5)))⟩

/-- **P0（C）、U0: 修正前の関数は、送るヘッダの最後の4バイトに入口の `enc->mask`（`m0`）を使い、戻ったあとも `enc->mask` は `m0`。**
    前提（`payload_len` が負でない、`payload_remain` が正でない、`*enc` の所有）を満たす入口のメモリがあることも示す（`cE`・`mE`）。
    同じ接続で続けて送るフレームは、`enc->mask` が変わらないので、同じマスクを使う。 -/
theorem P0_C :
    ∃ c : Ctx, (∃ hp m, encPre c hp ∧ Heap.Agrees hp m)
      ∧ Integers.Int64.lt c.pl (Integers.Int64.repr 0) = false
      ∧ Integers.Int64.lt (Integers.Int64.repr 0) c.rem = false
      ∧ IsPtr c.dataV ∧ IsPtr c.outV ∧ c.m0.length = 4
      ∧ ∀ ge : CGenv, ge.genv_cenv = Deb2025_10148_up_before.prog.prog_comp_env → ExtB ge c.encB c.m0 →
          ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal F0) (specB c) vs := by
  obtain ⟨hp, hH, hag⟩ := encPre_cE_satisfiable
  refine ⟨cE, ⟨hp, mE, hH, hag⟩, by decide, by decide, Or.inr ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩, rfl, ?_⟩
  intro ge hcenv X vs
  exact add_frame_before ge hcenv cE X (by decide) (by decide) (Or.inr ⟨_, rfl⟩) (Or.inr ⟨_, rfl⟩) rfl vs

end Deb2025_10148C
