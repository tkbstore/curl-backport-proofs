/-
CVE-2025-10148: Debian のバックポート（D1: curl 8.14.1 に CVE-2025-10148.patch を当てたもの）の `ws_enc_write_head`。

証明すること（`write_head_after`、P1）: U1（`Deb2025_10148After.lean` の `add_frame_after`）と同じ形。`Curl_bufq_write` に渡すヘッダの
最後の4バイトは、この呼び出しの中で `Curl_rand` が `enc->mask` に書いた4バイト `rb`（`bufqSpecD` の前提）。

8.14.1 の関数は上流と形が違う（戻り値は `ssize_t`、エラーは出力引数 `CURLcode *err`、局所変数は `head` だけで `firstbyte`・`n` は
一時変数、`ws_frame_flags2firstbyte` は先頭バイトを戻り値で返し、`Curl_bufq_write` は書いた長さを戻り値で返す）。
そのため U1 の証明を等式で移すことはできず、U1 の各文の証明を写して書き換えた。ヘッダの組み立て（本体の 10 番目の文）は
U1 と同じ文なので、`hdr` をそのまま使う。
-/
import Deb2025_10148After
import GenDeb2025_10148DebAfter
open CC CC.Sep CC.HProp
open Deb2025_10148_deb_after
open Case5C (RR boolVal_ofBool_tint)
open Case4debC (IsPtr cast_ptr)
open Deb2026_3805C (call2 set2 call_none heap_eq heap_imp triple_lift temps_weak once_loop int_eq_false ex_map)

set_option maxRecDepth 20000
set_option maxHeartbeats 400000

namespace Deb2025_10148C

theorem cenv_deb_after_same : Deb2025_10148_deb_after.prog.prog_comp_env
    = Deb2025_10148_up_after.prog.prog_comp_env := rfl

abbrev FD1 : Function := Deb2025_10148_deb_after.f_ws_enc_write_head
abbrev BD1 : Stmt := Deb2025_10148_deb_after.f_ws_enc_write_head.fn_body

/-- ヘッダの組み立ては U1 と同じ文。 -/
theorem hdr_same_d1 : hdS (sp 10 BD1) = hdS (sp 10 B1) := rfl

macro "unfD1" : tactic => `(tactic| (conv => arg 5; dsimp only [Deb2025_10148C.hdS, Deb2025_10148C.sp,
  Deb2025_10148C.BD1, Deb2025_10148_deb_after.f_ws_enc_write_head]))

/-! ## 局所変数と出力引数 `err` -/

def envD (hb : Block) : Env := emptyEnv.set _head (hb, tarray tuchar 14)

theorem envD_head (hb : Block) : (envD hb).get _head = some (hb, tarray tuchar 14) := rfl

theorem blocks_envD (ge : CGenv) (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (hb : Block) :
    blocksOfEnv ge.genv_cenv (envD hb) = [(hb, 0, 14)] := by
  rw [hcenv]; rfl

/-- `*err`（4バイト）と局所変数 `head`。 -/
abbrev LUD (errB hb : Block) : HProp := AB errB 0 4 ∗ AB hb 0 14

abbrev LkD (c : Ctx) (errB : Block) : List (Ident × Val) := (_err, .Vptr errB Integers.Ptrofs.zero) :: Lk c

abbrev L4D (c : Ctx) (errB : Block) (x : Integers.Int) : List (Ident × Val) :=
  (_firstbyte, .Vint (Integers.Int.zero_ext 8 x)) :: LkD c errB

abbrev L13D (c : Ctx) (errB : Block) (n : Nat) : List (Ident × Val) :=
  (_hlen, .Vlong (Integers.Int64.repr n)) :: LkD c errB

abbrev L16D (c : Ctx) (errB : Block) (n : Nat) : List (Ident × Val) :=
  (_hlen, .Vlong (Integers.Int64.repr ((n : Z) + 4))) :: LkD c errB

abbrev K4D (c : Ctx) (hb : Block) : HProp := AB hb 0 14 ∗ encA c.encB (mk0 c) (wd32 c c.w)
abbrev K6D (c : Ctx) (hb : Block) : HProp := AB hb 0 14 ∗ encA c.encB (mk0 c) (AB c.encB 24 4)
abbrev K13D (c : Ctx) (errB hb : Block) : HProp :=
  LUD errB hb ∗ AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ AB c.encB 24 4
abbrev K15D (c : Ctx) (errB hb : Block) (n : Nat) : HProp :=
  AB hb 0 n ∗ AB hb ((n : Z) + 4) (10 - n) ∗ AB errB 0 4
  ∗ AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ AB c.encB 24 4
abbrev K18D (c : Ctx) (rb : List MemVal) : HProp :=
  bytesPtsTo c.encB .Freeable 20 rb ∗ AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ AB c.encB 24 4
abbrev K13D' (c : Ctx) (hb : Block) : HProp :=
  AB hb 0 14 ∗ AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ AB c.encB 24 4

macro "acxD" : tactic => `(tactic| (
  (try simp only [Deb2025_10148C.encPre, Deb2025_10148C.encA, Deb2025_10148C.LUD, Deb2025_10148C.mk0,
    Deb2025_10148C.wd32, Deb2025_10148C.K4D, Deb2025_10148C.K6D, Deb2025_10148C.K10, Deb2025_10148C.K13D,
    Deb2025_10148C.K15D, Deb2025_10148C.K18D, Deb2025_10148C.K13D', Deb2025_10148C.encPost]) <;> ac_rfl))

/-! ## 外部関数の仕様（8.14.1 の型。弱く書く） -/

/-- `ws_frame_flags2firstbyte(data, flags, contfragment, err)`: 何かの1バイトを返し、`*err` に何かのコードを書く。 -/
def fbSpecD (errB : Block) : FunSpec where
  tyargs := [tptr easyT, tuint, tbool, tptr tint]
  tyres := tuchar
  cc := cc_default
  pre := fun vargs hp => (∃ a b c, vargs = [a, b, c, .Vptr errB Integers.Ptrofs.zero]) ∧ AB errB 0 4 hp
  post := fun v hp => ∃ x code, v = .Vint x ∧ mapsto .Mint32 .Freeable errB 0 (.Vint code) hp
  measure := fun _ => 0

/-- `Curl_bufq_write(out, head, n + 4, err)`（8.14.1 の型）。**前提に P1 を書く**: 渡すヘッダの最後の4バイト（`head[n .. n+4)`）が `mb`。
    何かの長さを返し、`*err` に何かを書く。 -/
def bufqSpecD (hb : Block) (n : Nat) (mb : List MemVal) (errB : Block) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _bufq noattr), tptr tuchar, tulong, tptr tint]
  tyres := tlong
  cc := cc_default
  pre := fun vargs hp => (∃ a, vargs = [a, .Vptr hb Integers.Ptrofs.zero,
      .Vlong (Integers.Int64.repr ((n : Z) + 4)), .Vptr errB Integers.Ptrofs.zero])
    ∧ (AB hb 0 n ∗ bytesPtsTo hb .Freeable n mb ∗ AB hb ((n : Z) + 4) (10 - n) ∗ AB errB 0 4) hp
  post := fun v hp => ∃ k, v = .Vlong k ∧ (AB hb 0 14 ∗ AB errB 0 4) hp
  measure := fun _ => 0

/-- 呼ばれる側の関数（D1）。`Curl_rand`・`memcpy`・`ws_enc_info`・`Curl_failf` の仕様は U1 と同じ。 -/
structure ExtD (ge : CGenv) (encB : Block) (rb : List MemVal) : Prop where
  fail : ∃ b fd, Genv.findSymbol ge.genv_genv _Curl_failf = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr easyT, tptr tschar] tvoid ccVar
    ∧ ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fd failSpec vs
  fb : ∃ b fd, Genv.findSymbol ge.genv_genv _ws_frame_flags2firstbyte = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr easyT, tuint, tbool, tptr tint] tuchar cc_default
    ∧ ∀ errB vs, SatisfiesAt ge (FunctionEntry2 ge) fd (fbSpecD errB) vs
  info : ∃ b fd, Genv.findSymbol ge.genv_genv _ws_enc_info = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr encT, tptr easyT, tptr tschar] tvoid cc_default
    ∧ ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fd infoSpec vs
  rand : ∃ b fd, Genv.findSymbol ge.genv_genv _Curl_rand_bytes = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr easyT, tptr tuchar, tulong] tint cc_default
    ∧ ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fd (randSpec encB rb) vs
  cpy : ∃ b fd, Genv.findSymbol ge.genv_genv _memcpy = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr tvoid, tptr tvoid, tulong] (tptr tvoid) cc_default
    ∧ ∀ hb n mb vs, SatisfiesAt ge (FunctionEntry2 ge) fd (cpySpec hb n encB mb) vs
  bufq : ∃ b fd, Genv.findSymbol ge.genv_genv _Curl_bufq_write = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr (Ty.Tstruct _bufq noattr), tptr tuchar, tulong, tptr tint] tlong cc_default
    ∧ ∀ hb n errB vs, SatisfiesAt ge (FunctionEntry2 ge) fd (bufqSpecD hb n rb errB) vs
  lit3 : ∃ b, Genv.findSymbol ge.genv_genv ___stringlit_3 = some b
  lit4 : ∃ b, Genv.findSymbol ge.genv_genv ___stringlit_4 = some b
  lit5 : ∃ b, Genv.findSymbol ge.genv_genv ___stringlit_5 = some b
  lit6 : ∃ b, Genv.findSymbol ge.genv_genv ___stringlit_6 = some b

/-! ## 事後条件と return -/

/-- 事後条件（D1）: `*enc` と `*err` の所有を返す（`mask` の中身は問わない）。戻り値は問わない。 -/
def postDA (c : Ctx) (errB : Block) : Val → HProp := fun _ hp =>
  (encPost c.encB (AB c.encB 20 4) ∗ AB errB 0 4) hp

/-- 局所変数 `head` を手放して return する（戻り値は `ssize_t` への変換で `v` から `v'` になる）。 -/
theorem retD (ge : CGenv) (fe) (f : Function) (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env)
    (errB hb : Block) (l : List (Ident × Val)) (Hk : HProp) (a : Expr) (v v' : Val) (Ret : Val → HProp)
    (Q : Sep.Assn)
    (hev : ∀ le m, TempsHold l le → EvalExpr ge (envD hb) le m a v)
    (hcast : ∀ m, Cop.semCast v (typeof a) f.fn_return m = some v')
    (hret : ∀ hp, (Hk ∗ AB errB 0 4) hp → Ret v' hp) :
    Triple ge fe f (LocalSt (envD hb) l (Hk ∗ LUD errB hb)) (.Sreturn (some a)) (RR Ret Q) := by
  have he : Hk ∗ LUD errB hb = (Hk ∗ AB errB 0 4) ∗ Case3C.Locs [(hb, 14)] := by
    simp only [Case3C.Locs, sep_emp_eq]; acxD
  rw [he]
  refine triple_conseq ge fe f
    (Case3C.ret_locs ge fe f (envD hb) l _ [(hb, 14)] a v v' Ret
      (fun le m _ hT _ _ => hev le m hT) hcast ?_ ?_ hret)
    (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
  · rw [blocks_envD ge hcenv]
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    subst hx
    exact ⟨hb, 14, rfl, by simp⟩
  · rw [blocks_envD ge hcenv]
    exact List.Pairwise.cons (fun _ h => by simp at h) List.Pairwise.nil

/-- 書き込むだけのセルへの代入。代入の後は値の分かる `mapsto` として持つ。 -/
theorem store_mk (ge fe f) (E : Env) (l : List (Ident × Val)) (R : HProp)
    (a1 a2 : Expr) (chunk : Chunk) (b : Block) (ofs : Integers.Ptrofs) (o : Z) (vnew : Val)
    (hacc : accessMode (typeof a1) = .By_value chunk)
    (ho : Integers.Ptrofs.unsigned ofs = o) (hal : o % alignChunk chunk = 0)
    (hlv : ∀ le m, TempsHold l le → EvalLvalue ge E le m a1 b ofs .Full)
    (hev : ∀ le m, TempsHold l le →
      ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some vnew) :
    Triple ge fe f (LocalSt E l (anyBytes .Freeable b o (sizeChunkNat chunk) ∗ R)) (.Sassign a1 a2)
      (.only (LocalSt E l (mapsto chunk .Freeable b o vnew ∗ R))) := by
  subst ho
  refine triple_assign_any ge fe f _ _ a1 a2 chunk .Freeable b ofs (by decide) hacc
    (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, h1, h2, hd, heq, hm, hr⟩ := hP
  subst he
  obtain ⟨v2, hev2, hc⟩ := hev le m hT
  exact ⟨vnew, h1, h2, hd, heq, hm, hal, hlv le m hT, ⟨v2, hev2, hc⟩,
    fun h1' hm' hd' => ⟨rfl, hT, h1', h2, hd', rfl, hm', hr⟩⟩

/-- `*err`（`err` は一時変数で、ブロック `errB` の先頭を指す）。 -/
theorem lv_err {ge : CGenv} {E : Env} {le : TempEnv} {m : Mem} {errB : Block}
    (hle : le.get _err = some (.Vptr errB Integers.Ptrofs.zero)) :
    EvalLvalue ge E le m (.Ederef (.Etempvar _err (tptr tint)) tint) errB Integers.Ptrofs.zero .Full :=
  EvalLvalue.Ederef _ _ _ _ (EvalExpr.Etempvar _ _ _ hle)

theorem post_AD (c : Ctx) (errB : Block) (hm0 : c.m0.length = 4) (wd : HProp)
    (hwd : ∀ h, wd h → AB c.encB 24 4 h) (v : Val) (hp : Heap)
    (h : (encA c.encB (mk0 c) wd ∗ AB errB 0 4) hp) : postDA c errB v hp :=
  sep_imp_l (fun h x => post_A c hm0 wd hwd v h x) h

/-- `Curl_rand` の戻り値 `r` に応じた `enc->mask` の4バイト。 -/
def mkR (encB : Block) (rb : List MemVal) (r : Integers.Int) : HProp := fun hp =>
  (r = Integers.Int.zero ∧ bytesPtsTo encB .Freeable 20 rb hp) ∨ (r ≠ Integers.Int.zero ∧ AB encB 20 4 hp)


/-- 出口（D1）: `mask` の中身を忘れる。 -/
theorem fin_heapD (c : Ctx) (errB hb : Block) (rb : List MemVal) (hrb : rb.length = 4) (hp : Heap)
    (h : ((AB hb 0 14 ∗ AB errB 0 4) ∗ K18D c rb) hp) :
    (encPost c.encB (AB c.encB 20 4) ∗ LUD errB hb) hp := by
  have e1 : (AB hb 0 14 ∗ AB errB 0 4) ∗ K18D c rb = bytesPtsTo c.encB .Freeable 20 rb
      ∗ (AB hb 0 14 ∗ AB errB 0 4 ∗ AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ AB c.encB 24 4) := by acxD
  rw [e1] at h
  exact conv1 (P' := AB c.encB 20 4) (fun _ y => mk_any hrb y) (by acxD) h

section
variable (ge : CGenv) (c : Ctx) (errB hb : Block)

def P0D : Sep.Assn := LocalSt (envD hb) (LkD c errB) (encPre c ∗ LUD errB hb)

theorem s0D :
    Triple ge (FunctionEntry2 ge) FD1 (P0D c errB hb) (hdS (sp 0 BD1))
      (RR (postDA c errB) (P0D c errB hb)) := by
  unfD1
  unfold P0D
  refine post_to ge _ _ _ (set2 ge _ _ _ _ _ _firstbyte _ (.Vint Integers.Int.zero) (by lf)
    (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)) ?_
  exact fun e le hp ⟨he, hT, hH⟩ => ⟨he, TempsHold_mono (by ls) hT, hH⟩

theorem s1D (hpl : Integers.Int64.lt c.pl (Integers.Int64.repr 0) = false) :
    Triple ge (FunctionEntry2 ge) FD1 (P0D c errB hb) (hdS (sp 1 BD1))
      (RR (postDA c errB) (P0D c errB hb)) := by
  unfD1
  unfold P0D
  refine if_val ge _ _ _ _ _ _ false _ _ _ (Val.ofBool false) ?_ (fun m => boolVal_ofBool_tint _ m) ?_
  · intro le m hp hT _ _
    refine EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm)))
      (EvalExpr.Econst_int _ _) ?_
    show some (Val.ofBool (Integers.Int64.lt c.pl (Integers.Int64.repr 0))) = _
    rw [hpl]
  · exact skip_to ge _ _ _ _ _ (fun _ _ _ x => x)

def P3D : Sep.Assn := LocalSt (envD hb) ((_t'13, .Vlong c.rem) :: LkD c errB)
  (encA c.encB (mk0 c) (wd32 c c.w) ∗ LUD errB hb)

theorem s2D (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env)
    (hrem : Integers.Int64.lt (Integers.Int64.repr 0) c.rem = false) :
    Triple ge (FunctionEntry2 ge) FD1 (P0D c errB hb) (hdS (sp 2 BD1))
      (RR (postDA c errB) (P3D c errB hb)) := by
  unfD1
  unfold P0D
  have he : encPre c ∗ LUD errB hb = mapsto .Mint64 .Freeable c.encB 8 (.Vlong c.rem)
      ∗ (AB c.encB 0 8 ∗ AB c.encB 16 4 ∗ mk0 c ∗ wd32 c c.w ∗ LUD errB hb) := by
    unfold encPre; acxD
  refine triple_seq_fwd ge _ _ _
    (LocalSt (envD hb) ((_t'13, .Vlong c.rem) :: LkD c errB) (encPre c ∗ LUD errB hb)) _ _ _ ?_ ?_
  · refine set2 ge _ _ _ _ _ _t'13 _ (.Vlong c.rem) (by lf) ?_
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
def P4D : Sep.Assn := fun e le hp => ∃ x code,
  LocalSt (envD hb) ((_firstbyte, .Vint (Integers.Int.zero_ext 8 x)) :: (_t'1, .Vint x)
      :: (_t'12, cfV c) :: (_t'13, .Vlong c.rem) :: LkD c errB)
    (mapsto .Mint32 .Freeable errB 0 (.Vint code) ∗ K4D c hb) e le hp

theorem s3D (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (rb : List MemVal)
    (X : ExtD ge c.encB rb) (hdata : IsPtr c.dataV) :
    Triple ge (FunctionEntry2 ge) FD1 (P3D c errB hb) (hdS (sp 3 BD1))
      (RR (postDA c errB) (P4D c errB hb)) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.fb
  refine only_RR _ _ _ _ ?_
  unfD1
  unfold P3D
  have hw : encA c.encB (mk0 c) (wd32 c c.w) ∗ LUD errB hb = wd32 c c.w
      ∗ (AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ mk0 c ∗ LUD errB hb) := by acxD
  have hf : encA c.encB (mk0 c) (wd32 c c.w) ∗ LUD errB hb = AB errB 0 4 ∗ K4D c hb := by
    acxD
  refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ v, LocalSt (envD hb)
      ((_t'1, v) :: (_t'12, cfV c) :: (_t'13, .Vlong c.rem) :: LkD c errB)
      ((fbSpecD errB).post v ∗ K4D c hb) e le hp) _ _ _ ?_ ?_
  · refine triple_seq_fwd ge _ _ _ (LocalSt (envD hb)
      ((_t'12, cfV c) :: (_t'13, .Vlong c.rem) :: LkD c errB)
      (encA c.encB (mk0 c) (wd32 c c.w) ∗ LUD errB hb)) _ _ _ ?_ ?_
    · refine set2 ge _ _ _ _ _ _t'12 _ (cfV c) (by lf) ?_
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
      ∧ LocalSt (envD hb) ((_t'1, x.1) :: (_t'12, cfV c) :: (_t'13, .Vlong c.rem) :: LkD c errB)
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

def P5D : Sep.Assn := fun e le hp => ∃ x, LocalSt (envD hb) (L4D c errB x)
  (AB errB 0 4 ∗ K4D c hb) e le hp

theorem s4D (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (hm0 : c.m0.length = 4) :
    Triple ge (FunctionEntry2 ge) FD1 (P4D c errB hb) (hdS (sp 4 BD1))
      (RR (postDA c errB) (P5D c errB hb)) := by
  unfD1
  refine triple_lift ge _ _ (fun y : Integers.Int × Integers.Int => LocalSt (envD hb)
      ((_firstbyte, .Vint (Integers.Int.zero_ext 8 y.1)) :: (_t'1, .Vint y.1)
        :: (_t'12, cfV c) :: (_t'13, .Vlong c.rem) :: LkD c errB)
      (mapsto .Mint32 .Freeable errB 0 (.Vint y.2) ∗ K4D c hb)) _ _ _
    (fun e le hp ⟨x, code, h⟩ => ⟨(x, code), h⟩) (fun ⟨x, code⟩ => ?_)
  refine triple_seq_fwd ge _ _ _ (LocalSt (envD hb) ((_t'11, .Vint code)
      :: (_firstbyte, .Vint (Integers.Int.zero_ext 8 x)) :: (_t'1, .Vint x)
        :: (_t'12, cfV c) :: (_t'13, .Vlong c.rem) :: LkD c errB)
      (mapsto .Mint32 .Freeable errB 0 (.Vint code) ∗ K4D c hb)) _ _ _ ?_ ?_
  · refine set2 ge _ _ _ _ _ _t'11 _ _ (by lf) (fun le m hp hT hH hag => ?_)
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
      (fun hp h => post_AD c errB hm0 _ (fun _ x => mapsto_anyB x) _ hp h)

def P6D : Sep.Assn := fun e le hp => ∃ x, LocalSt (envD hb) (L4D c errB x)
  (AB errB 0 4 ∗ K6D c hb) e le hp

theorem s5D (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) :
    Triple ge (FunctionEntry2 ge) FD1 (P5D c errB hb) (hdS (sp 5 BD1))
      (RR (postDA c errB) (P6D c errB hb)) := by
  unfD1
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

theorem s6D (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (rb : List MemVal)
    (X : ExtD ge c.encB rb) (hdata : IsPtr c.dataV) (hm0 : c.m0.length = 4) :
    Triple ge (FunctionEntry2 ge) FD1 (P6D c errB hb) (hdS (sp 6 BD1))
      (RR (postDA c errB) (P6D c errB hb)) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.fail
  obtain ⟨bL, hsL⟩ := X.lit3
  unfD1
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
          (fun hp h => post_AD c errB hm0 _ (fun _ y => y) _ hp h)

theorem s7D (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (rb : List MemVal)
    (X : ExtD ge c.encB rb) (hdata : IsPtr c.dataV) (hm0 : c.m0.length = 4) :
    Triple ge (FunctionEntry2 ge) FD1 (P6D c errB hb) (hdS (sp 7 BD1))
      (RR (postDA c errB) (P6D c errB hb)) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.fail
  obtain ⟨bL, hsL⟩ := X.lit4
  unfD1
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
          (fun hp h => post_AD c errB hm0 _ (fun _ y => y) _ hp h)

theorem s8D (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (rb : List MemVal)
    (X : ExtD ge c.encB rb) (hdata : IsPtr c.dataV) (hm0 : c.m0.length = 4) :
    Triple ge (FunctionEntry2 ge) FD1 (P6D c errB hb) (hdS (sp 8 BD1))
      (RR (postDA c errB) (P6D c errB hb)) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.fail
  obtain ⟨bL, hsL⟩ := X.lit5
  unfD1
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
          (fun hp h => post_AD c errB hm0 _ (fun _ y => y) _ hp h)

def P10D : Sep.Assn := LocalSt (envD hb) (LkD c errB) (LUD errB hb ∗ K10 c)

theorem s9D (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) :
    Triple ge (FunctionEntry2 ge) FD1 (P6D c errB hb) (hdS (sp 9 BD1))
      (RR (postDA c errB) (P10D c errB hb)) := by
  unfD1
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

def P11D : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ LocalSt (envD hb) (L13D c errB n) (LUD errB hb ∗ K10 c) e le hp

theorem s10D :
    Triple ge (FunctionEntry2 ge) FD1 (P10D c errB hb) (hdS (sp 10 BD1))
      (RR (postDA c errB) (P11D c errB hb)) := by
  rw [hdr_same_d1]
  unfold P10D
  have hq : LUD errB hb ∗ K10 c = AB hb 0 14 ∗ (AB errB 0 4 ∗ K10 c) := by acxD
  rw [hq]
  refine temps_weak ge _ _ _ _ ((_payload_len, .Vlong c.pl) :: LkD c errB) _ _ _
    (by ls) ?_
  refine triple_conseq ge _ _ (hdr ge _ _ _ _ c.pl _ (postDA c errB) hb (envD_head _) (by lf))
    (fun _ _ _ x => x) ?_ (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
  intro e le hp ⟨n, hn, he, hT, hH⟩
  exact ⟨n, hn, he, TempsHold_mono (by ls) hT, by rw [hq]; exact hH⟩

/-- `P11D` の `n` を取り出す。 -/
theorem lift_nD (P : Nat → Sep.Assn) (s : Stmt) (R : Sep.ExitConds)
    (h : ∀ n, (n = 2 ∨ n = 4 ∨ n = 10) → Triple ge (FunctionEntry2 ge) FD1 (P n) s R) :
    Triple ge (FunctionEntry2 ge) FD1 (fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10) ∧ P n e le hp) s R := by
  intro k e le hp hf m hd hag ⟨n, hn, hP⟩
  exact h n hn k e le hp hf m hd hag hP

theorem s11D (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) :
    Triple ge (FunctionEntry2 ge) FD1 (P11D c errB hb) (hdS (sp 11 BD1))
      (RR (postDA c errB) (P11D c errB hb)) := by
  unfD1
  refine lift_nD ge _ _ _ (fun n hn => ?_)
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

theorem s12D (rb : List MemVal) (X : ExtD ge c.encB rb) (hdata : IsPtr c.dataV) :
    Triple ge (FunctionEntry2 ge) FD1 (P11D c errB hb) (hdS (sp 12 BD1))
      (RR (postDA c errB) (P11D c errB hb)) := by
  obtain ⟨bI, fdI, hsI, hfI, htI, hI⟩ := X.info
  obtain ⟨bL, hsL⟩ := X.lit6
  unfD1
  refine lift_nD ge _ _ _ (fun n hn => ?_)
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

def P13D (rb : List MemVal) : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ ∃ r, LocalSt (envD hb) ((_t'8, .Vint r) :: L13D c errB n)
    (mapsto .Mint32 .Freeable errB 0 (.Vint r) ∗ (mkR c.encB rb r ∗ K13D' c hb)) e le hp

theorem s13D (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (rb : List MemVal)
    (X : ExtD ge c.encB rb) (hdata : IsPtr c.dataV) (hm0 : c.m0.length = 4) :
    Triple ge (FunctionEntry2 ge) FD1 (P11D c errB hb) (hdS (sp 13 BD1))
      (RR (postDA c errB) (P13D c errB hb rb)) := by
  obtain ⟨bR, fdR, hsR, hfR, htR, hR⟩ := X.rand
  unfD1
  refine lift_nD ge _ _ _ (fun n hn => ?_)
  refine post_to ge _ _ _ (Q := fun e le hp => ∃ r, LocalSt (envD hb) ((_t'8, .Vint r) :: L13D c errB n)
    (mapsto .Mint32 .Freeable errB 0 (.Vint r) ∗ (mkR c.encB rb r ∗ K13D' c hb)) e le hp) ?_
    (fun e le hp h => ⟨n, hn, h⟩)
  refine heap_imp ge _ _ _ _ _ (AB c.encB 20 4 ∗ K13D c errB hb) _ _
    (fun hp h => conv1 (P := mk0 c) (P' := AB c.encB 20 4) (R := K13D c errB hb) (fun _ y => mk_any hm0 y) (by acxD)
      (by have e : LUD errB hb ∗ K10 c = mk0 c ∗ K13D c errB hb := by acxD
          rw [e] at h; exact h)) ?_
  refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ v, LocalSt (envD hb) ((_t'8, v) :: L13D c errB n)
    ((randSpec c.encB rb).post v ∗ K13D c errB hb) e le hp) _ _ _ ?_ ?_
  · refine call2 ge _ _ (randSpec c.encB rb) _t'8 _ _ _ _ (AB c.encB 20 4) (K13D c errB hb)
      [c.dataV, .Vptr c.encB (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr 20)),
        .Vlong (Integers.Int64.repr 4)] bR fdR hR hfR htR ?hcl (by lf) ?hc ?ha ?hp
    case hcl => rfl
    case hc => exact fun _ _ _ => eval_callee_global rfl hsR rfl
    case ha =>
      intro le m hT
      exact EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (cast_ptr hdata _ _ _)
        (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Ecast _ _ _ _
          (EvalExpr.Eaddrof _ _ _ _ (lv_enc hcenv (hT.get (by lm)) off_mask)) rfl) rfl
        (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Esizeof _ _) rfl EvalExprlist.nil))
    case hp => exact fun h hh => ⟨⟨c.dataV, _, rfl, rfl⟩, hh⟩
  · refine triple_lift ge _ _ (fun x : Val × Integers.Int => fun e le hp => x.1 = .Vint x.2
      ∧ LocalSt (envD hb) ((_t'8, x.1) :: L13D c errB n) (mkR c.encB rb x.2 ∗ K13D c errB hb) e le hp)
      _ _ _ ?_ (fun ⟨v, r⟩ => ?_)
    · intro e le hp ⟨v, he, hT, h1, h2, hd, heq, ⟨r, hv, hor⟩, hk⟩
      exact ⟨(v, r), hv, he, hT, h1, h2, hd, heq, hor, hk⟩
    refine pure_l ge _ _ _ _ _ _ (fun hv => ?_)
    dsimp only at hv
    subst hv
    refine heap_eq ge _ _ _ _ _ (AB errB 0 4 ∗ (mkR c.encB rb r ∗ K13D' c hb)) _ _ (by acxD) ?_
    exact triple_conseq ge _ _ (store_mk ge _ _ _ _ _ _ _ .Mint32 errB _ 0 (.Vint r) rfl rfl rfl
      (fun le m hT => lv_err (hT.get (by lm)))
      (fun le m hT => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by lm)), rfl⟩))
      (fun _ _ _ x => x) (fun e le hp h => ⟨r, h⟩)
      (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)

def P14D (rb : List MemVal) : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ LocalSt (envD hb) (L13D c errB n) (bytesPtsTo c.encB .Freeable 20 rb ∗ K13D c errB hb) e le hp

theorem s14D (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (rb : List MemVal) :
    Triple ge (FunctionEntry2 ge) FD1 (P13D c errB hb rb) (hdS (sp 14 BD1))
      (RR (postDA c errB) (P14D c errB hb rb)) := by
  unfD1
  refine lift_nD ge _ _ _ (fun n hn => ?_)
  refine triple_lift ge _ _ (fun r => LocalSt (envD hb) ((_t'8, .Vint r) :: L13D c errB n)
    (mapsto .Mint32 .Freeable errB 0 (.Vint r) ∗ (mkR c.encB rb r ∗ K13D' c hb))) _ _ _
    (fun e le hp h => h) (fun r => ?_)
  refine triple_seq_fwd ge _ _ _ (LocalSt (envD hb) ((_t'10, .Vint r) :: (_t'8, .Vint r) :: L13D c errB n)
    (mapsto .Mint32 .Freeable errB 0 (.Vint r) ∗ (mkR c.encB rb r ∗ K13D' c hb))) _ _ _ ?_ ?_
  · refine set2 ge _ _ _ _ _ _t'10 _ _ (by lf) (fun le m hp hT hH hag => ?_)
    refine EvalExpr.Elvalue _ _ _ .Full _ (lv_err (hT.get (by lm))) (DerefLoc.value .Mint32 _ rfl ?_)
    show Mem.load .Mint32 m errB 0 = _
    exact cell_ld rfl hH hag
  by_cases hr : r = Integers.Int.zero
  · subst hr
    refine if_val ge _ _ _ _ _ _ false _ _ _ (.Vint Integers.Int.zero)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (fun m => rfl) ?_
    refine skip_to ge _ _ _ _ _ (fun e le hp ⟨he, hT, hH⟩ => ⟨n, hn, he, TempsHold_mono (by ls) hT, ?_⟩)
    have h1 := sep_imp_l (P' := AB errB 0 4) (fun _ y => mapsto_anyB (chunk := .Mint32) y) hH
    have e1 : AB errB 0 4 ∗ (mkR c.encB rb Integers.Int.zero ∗ K13D' c hb)
        = mkR c.encB rb Integers.Int.zero ∗ K13D c errB hb := by acxD
    rw [e1] at h1
    exact sep_imp_l (fun _ y => by
      rcases y with ⟨_, yb⟩ | ⟨yn, _⟩
      · exact yb
      · exact absurd rfl yn) h1
  · refine if_val ge _ _ _ _ _ _ true _ _ _ (.Vint r)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm)))
      (fun m => by show some (!Integers.Int.eq r Integers.Int.zero) = _; rw [int_eq_false hr]; rfl) ?_
    refine heap_imp ge _ _ _ _ _ (encPost c.encB (AB c.encB 20 4) ∗ LUD errB hb) _ _ (fun hp h => ?_) ?_
    · have h1 := sep_imp_l (P' := AB errB 0 4) (fun _ y => mapsto_anyB (chunk := .Mint32) y) h
      have e1 : AB errB 0 4 ∗ (mkR c.encB rb r ∗ K13D' c hb)
          = mkR c.encB rb r ∗ (AB errB 0 4 ∗ K13D' c hb) := by acxD
      rw [e1] at h1
      exact conv1 (P' := AB c.encB 20 4) (fun _ y => by
        rcases y with ⟨y0, _⟩ | ⟨_, ya⟩
        · exact absurd y0 hr
        · exact ya) (by acxD) h1
    exact retD ge _ _ hcenv errB hb _ _ _ _ _ _ _ (fun le m hT => by evx) (fun _ => by rfl)
      (fun hp h => h)

def P15D (rb : List MemVal) : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ ∃ v, LocalSt (envD hb) (L13D c errB n)
    ((cpySpec hb n c.encB rb).post v ∗ K15D c errB hb n) e le hp

theorem s15D (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (rb : List MemVal)
    (X : ExtD ge c.encB rb) :
    Triple ge (FunctionEntry2 ge) FD1 (P14D c errB hb rb) (hdS (sp 15 BD1))
      (RR (postDA c errB) (P15D c errB hb rb)) := by
  obtain ⟨bC, fdC, hsC, hfC, htC, hC⟩ := X.cpy
  unfD1
  refine lift_nD ge _ _ _ (fun n hn => ?_)
  refine post_to ge _ _ _ (Q := fun e le hp => ∃ v, LocalSt (envD hb) (L13D c errB n)
    ((cpySpec hb n c.encB rb).post v ∗ K15D c errB hb n) e le hp) ?_ (fun e le hp h => ⟨n, hn, h⟩)
  have hq : bytesPtsTo c.encB .Freeable 20 rb ∗ K13D c errB hb
      = (AB hb n 4 ∗ bytesPtsTo c.encB .Freeable 20 rb) ∗ K15D c errB hb n := by
    simp only [K13D, LUD]; rw [head_split hb n (hn_le hn)]; acxD
  rw [hq]
  refine call_none_ex ge _ _ (cpySpec hb n c.encB rb) _ _ _ _ _ _ bC fdC (hC hb n rb) hfC htC rfl
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

def P16D (rb : List MemVal) : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ LocalSt (envD hb) (L16D c errB n)
    ((bytesPtsTo hb .Freeable n rb ∗ bytesPtsTo c.encB .Freeable 20 rb) ∗ K15D c errB hb n) e le hp

theorem s16D (rb : List MemVal) :
    Triple ge (FunctionEntry2 ge) FD1 (P15D c errB hb rb) (hdS (sp 16 BD1))
      (RR (postDA c errB) (P16D c errB hb rb)) := by
  unfD1
  refine lift_nD ge _ _ _ (fun n hn => ?_)
  refine triple_lift ge _ _ (fun v => LocalSt (envD hb) (L13D c errB n)
    ((cpySpec hb n c.encB rb).post v ∗ K15D c errB hb n)) _ _ _ (fun e le hp h => h) (fun v => ?_)
  refine post_to ge _ _ _ (triple_set_local ge _ _ _ (L13D c errB n) (LkD c errB) _ _hlen _
    (.Vlong (Integers.Int64.repr ((n : Z) + 4))) (by ls) (by lf) (fun le m hp hT _ _ => ?_)) ?_
  · refine EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..)))
      (EvalExpr.Econst_int _ _) ?_
    rcases hn with rfl | rfl | rfl <;> rfl
  · exact fun e le hp h => ⟨n, hn, h⟩

theorem s17D (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (rb : List MemVal) :
    Triple ge (FunctionEntry2 ge) FD1 (P16D c errB hb rb) (hdS (sp 17 BD1))
      (RR (postDA c errB) (P16D c errB hb rb)) := by
  unfD1
  refine lift_nD ge _ _ _ (fun n hn => ?_)
  refine post_to ge _ _ _ ?_ (fun e le hp h => ⟨n, hn, h⟩)
  have hq : (bytesPtsTo hb .Freeable n rb ∗ bytesPtsTo c.encB .Freeable 20 rb) ∗ K15D c errB hb n
      = AB c.encB 16 4 ∗ (bytesPtsTo hb .Freeable n rb ∗ bytesPtsTo c.encB .Freeable 20 rb ∗ AB hb 0 n
        ∗ AB hb ((n : Z) + 4) (10 - n) ∗ AB errB 0 4 ∗ AB c.encB 0 8 ∗ AB c.encB 8 8
        ∗ AB c.encB 24 4) := by acxD
  rw [hq]
  exact store_any ge _ _ _ _ _ _ _ .Mint32 c.encB _ 16 rfl rfl rfl
    (fun le m hT => lv_enc hcenv (hT.get (by lm)) off_xori)
    (fun le m hT => ⟨_, _, EvalExpr.Econst_int _ _, rfl⟩)

def P18D (rb : List MemVal) : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ ∃ v, LocalSt (envD hb) ((_n, v) :: (_t'9, v) :: L16D c errB n)
    ((bufqSpecD hb n rb errB).post v ∗ K18D c rb) e le hp

theorem s18D (rb : List MemVal) (X : ExtD ge c.encB rb) (hout : IsPtr c.outV) :
    Triple ge (FunctionEntry2 ge) FD1 (P16D c errB hb rb) (hdS (sp 18 BD1))
      (RR (postDA c errB) (P18D c errB hb rb)) := by
  obtain ⟨bQ, fdQ, hsQ, hfQ, htQ, hQ⟩ := X.bufq
  unfD1
  refine lift_nD ge _ _ _ (fun n hn => ?_)
  refine post_to ge _ _ _ (Q := fun e le hp => ∃ v, LocalSt (envD hb) ((_n, v) :: (_t'9, v) :: L16D c errB n)
    ((bufqSpecD hb n rb errB).post v ∗ K18D c rb) e le hp) ?_ (fun e le hp h => ⟨n, hn, h⟩)
  have hq : (bytesPtsTo hb .Freeable n rb ∗ bytesPtsTo c.encB .Freeable 20 rb) ∗ K15D c errB hb n
      = (AB hb 0 n ∗ bytesPtsTo hb .Freeable n rb ∗ AB hb ((n : Z) + 4) (10 - n) ∗ AB errB 0 4)
        ∗ K18D c rb := by acxD
  rw [hq]
  refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ v, LocalSt (envD hb) ((_t'9, v) :: L16D c errB n)
    ((bufqSpecD hb n rb errB).post v ∗ K18D c rb) e le hp) _ _ _ ?_ ?_
  · refine call2 ge _ _ (bufqSpecD hb n rb errB) _t'9 _ _ _ _ _ (K18D c rb)
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

def P19D (rb : List MemVal) : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ ∃ k, LocalSt (envD hb) ((_n, .Vlong k) :: L16D c errB n)
    ((AB hb 0 14 ∗ AB errB 0 4) ∗ K18D c rb) e le hp

theorem s19D (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (rb : List MemVal)
    (hrb : rb.length = 4) :
    Triple ge (FunctionEntry2 ge) FD1 (P18D c errB hb rb) (hdS (sp 19 BD1))
      (RR (postDA c errB) (P19D c errB hb rb)) := by
  unfD1
  refine lift_nD ge _ _ _ (fun n hn => ?_)
  refine triple_lift ge _ _ (fun x : Val × Integers.Int64 => fun e le hp => x.1 = .Vlong x.2
      ∧ LocalSt (envD hb) ((_n, x.1) :: (_t'9, x.1) :: L16D c errB n)
        ((AB hb 0 14 ∗ AB errB 0 4) ∗ K18D c rb) e le hp) _ _ _ ?_ (fun ⟨v, k⟩ => ?_)
  · intro e le hp ⟨v, he, hT, h1, h2, hd, heq, ⟨k, hv, hh⟩, hk⟩
    exact ⟨(v, k), hv, he, hT, h1, h2, hd, heq, hh, hk⟩
  refine pure_l ge _ _ _ _ _ _ (fun hv => ?_)
  dsimp only at hv
  subst hv
  refine if_both ge _ _ _ _ _ _ _ _ _ (fun le m hT =>
    ⟨Val.ofBool (Integers.Int64.lt k (Integers.Int64.repr (Integers.Int.signed (Integers.Int.repr 0)))), _,
      EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..)))
        (EvalExpr.Econst_int _ _) rfl, boolVal_ofBool_tint _ _⟩) ?_ ?_
  · refine heap_imp ge _ _ _ _ _ _ _ _ (fun hp h => fin_heapD c errB hb rb hrb hp h) ?_
    exact retD ge _ _ hcenv errB hb _ _ _ _ _ _ _ (fun le m hT => by evx) (fun _ => by rfl)
      (fun hp h => h)
  · exact skip_to ge _ _ _ _ _ (fun e le hp ⟨he, hT, hH⟩ => ⟨n, hn, k, he, TempsHold_mono (by ls) hT, hH⟩)

theorem s20D (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (rb : List MemVal)
    (hrb : rb.length = 4) :
    Triple ge (FunctionEntry2 ge) FD1 (P19D c errB hb rb) (hdS (sp 20 BD1))
      (RR (postDA c errB) (P19D c errB hb rb)) := by
  unfD1
  refine lift_nD ge _ _ _ (fun n hn => ?_)
  refine triple_lift ge _ _ (fun k => LocalSt (envD hb) ((_n, .Vlong k) :: L16D c errB n)
    ((AB hb 0 14 ∗ AB errB 0 4) ∗ K18D c rb)) _ _ _
    (fun e le hp h => h) (fun k => ?_)
  refine if_both ge _ _ _ _ _ _ _ _ _ (fun le m hT =>
    ⟨Val.ofBool (!Integers.Int64.eq k (Integers.Int64.repr ((n : Z) + 4))), _,
      EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..))) rfl)
        (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) rfl, boolVal_ofBool_tint _ _⟩) ?_ ?_
  · refine triple_seq_fwd ge _ _ _ _ _ _ _ (once_loop ge _ _ _ _ _ (triple_skip ge _ _ _)) ?_
    refine heap_eq ge _ _ _ _ _ (AB errB 0 4 ∗ (AB hb 0 14 ∗ K18D c rb)) _ _ (by acxD) ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (store_any ge _ _ _ _ _ _ _ .Mint32 errB _ 0 rfl rfl rfl
      (fun le m hT => lv_err (hT.get (by lm))) (fun le m hT => ⟨_, _, EvalExpr.Econst_int _ _, rfl⟩)) ?_
    refine heap_imp ge _ _ _ _ (AB errB 0 4 ∗ (AB hb 0 14 ∗ K18D c rb)) _ _ _
      (fun hp h => fin_heapD c errB hb rb hrb hp (by
        have e : AB errB 0 4 ∗ (AB hb 0 14 ∗ K18D c rb) = (AB hb 0 14 ∗ AB errB 0 4) ∗ K18D c rb := by acxD
        rw [e] at h; exact h)) ?_
    exact retD ge _ _ hcenv errB hb _ _ _ _ _ _ _ (fun le m hT => by evx) (fun _ => by rfl)
      (fun hp h => h)
  · exact skip_to ge _ _ _ _ _ (fun e le hp ⟨he, hT, hH⟩ => ⟨n, hn, k, he, hT, hH⟩)

theorem s21D (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (rb : List MemVal)
    (hrb : rb.length = 4) :
    Triple ge (FunctionEntry2 ge) FD1 (P19D c errB hb rb) (sp 21 BD1)
      (RR (postDA c errB) Sep.Assn.no) := by
  unfD1
  refine lift_nD ge _ _ _ (fun n hn => ?_)
  refine triple_lift ge _ _ (fun k => LocalSt (envD hb) ((_n, .Vlong k) :: L16D c errB n)
    ((AB hb 0 14 ∗ AB errB 0 4) ∗ K18D c rb)) _ _ _
    (fun e le hp h => h) (fun k => ?_)
  refine heap_imp ge _ _ _ _ _ _ _ _ (fun hp h => fin_heapD c errB hb rb hrb hp h) ?_
  exact retD ge _ _ hcenv errB hb _ _ _ (.Vlong k) (.Vlong k) _ _
    (fun le m hT => EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..))) (fun _ => rfl) (fun hp h => h)

end


/-! ## 本体と、関数の仕様（D1） -/

theorem body_dafter (ge : CGenv) (hcenv : ge.genv_cenv = Deb2025_10148_up_after.prog.prog_comp_env) (c : Ctx)
    (rb : List MemVal) (X : ExtD ge c.encB rb)
    (hpl : Integers.Int64.lt c.pl (Integers.Int64.repr 0) = false)
    (hrem : Integers.Int64.lt (Integers.Int64.repr 0) c.rem = false)
    (hdata : IsPtr c.dataV) (hout : IsPtr c.outV) (hm0 : c.m0.length = 4) (hrb : rb.length = 4)
    (errB hb : Block) :
    Triple ge (FunctionEntry2 ge) FD1 (P0D c errB hb) FD1.fn_body
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := postDA c errB } := by
  show Triple _ _ _ _ (sp 0 BD1) (RR (postDA c errB) Sep.Assn.no)
  refine chain ge _ _ BD1 0 _ _ _ _ rfl (s0D ge c errB hb) ?_
  refine chain ge _ _ BD1 1 _ _ _ _ rfl (s1D ge c errB hb hpl) ?_
  refine chain ge _ _ BD1 2 _ _ _ _ rfl (s2D ge c errB hb hcenv hrem) ?_
  refine chain ge _ _ BD1 3 _ _ _ _ rfl (s3D ge c errB hb hcenv rb X hdata) ?_
  refine chain ge _ _ BD1 4 _ _ _ _ rfl (s4D ge c errB hb hcenv hm0) ?_
  refine chain ge _ _ BD1 5 _ _ _ _ rfl (s5D ge c errB hb hcenv) ?_
  refine chain ge _ _ BD1 6 _ _ _ _ rfl (s6D ge c errB hb hcenv rb X hdata hm0) ?_
  refine chain ge _ _ BD1 7 _ _ _ _ rfl (s7D ge c errB hb hcenv rb X hdata hm0) ?_
  refine chain ge _ _ BD1 8 _ _ _ _ rfl (s8D ge c errB hb hcenv rb X hdata hm0) ?_
  refine chain ge _ _ BD1 9 _ _ _ _ rfl (s9D ge c errB hb hcenv) ?_
  refine chain ge _ _ BD1 10 _ _ _ _ rfl (s10D ge c errB hb) ?_
  refine chain ge _ _ BD1 11 _ _ _ _ rfl (s11D ge c errB hb hcenv) ?_
  refine chain ge _ _ BD1 12 _ _ _ _ rfl (s12D ge c errB hb rb X hdata) ?_
  refine chain ge _ _ BD1 13 _ _ _ _ rfl (s13D ge c errB hb hcenv rb X hdata hm0) ?_
  refine chain ge _ _ BD1 14 _ _ _ _ rfl (s14D ge c errB hb hcenv rb) ?_
  refine chain ge _ _ BD1 15 _ _ _ _ rfl (s15D ge c errB hb hcenv rb X) ?_
  refine chain ge _ _ BD1 16 _ _ _ _ rfl (s16D ge c errB hb rb) ?_
  refine chain ge _ _ BD1 17 _ _ _ _ rfl (s17D ge c errB hb hcenv rb) ?_
  refine chain ge _ _ BD1 18 _ _ _ _ rfl (s18D ge c errB hb rb X hout) ?_
  refine chain ge _ _ BD1 19 _ _ _ _ rfl (s19D ge c errB hb hcenv rb hrb) ?_
  refine chain ge _ _ BD1 20 _ _ _ _ rfl (s20D ge c errB hb hcenv rb hrb) ?_
  exact s21D ge c errB hb hcenv rb hrb

/-- 関数の仕様（D1）。前提: 引数がこの値で、`*enc` と `*err` を所有している。事後条件: その所有を返す。 -/
def specDA (c : Ctx) (errB : Block) : FunSpec where
  tyargs := [tptr easyT, tptr encT, tuint, tlong, tptr (Ty.Tstruct _bufq noattr), tptr tint]
  tyres := tlong
  cc := cc_default
  pre := fun vargs hp => vargs = [c.dataV, .Vptr c.encB Integers.Ptrofs.zero, .Vint c.fl, .Vlong c.pl, c.outV,
      .Vptr errB Integers.Ptrofs.zero]
    ∧ (encPre c ∗ AB errB 0 4) hp
  post := postDA c errB
  measure := fun _ => 0

theorem write_head_after_entry_wf :
    listNorepet (varNames FD1.fn_vars) ∧ listNorepet (varNames FD1.fn_params)
    ∧ listDisjoint (varNames FD1.fn_params) (varNames FD1.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **Debian のバックポート（D1）の `ws_enc_write_head`**: U1 の `add_frame_after` と同じ形。`Curl_rand` が `enc->mask` に `rb` を
    書くとき、`Curl_bufq_write` に渡すヘッダの最後の4バイトは `rb`（`bufqSpecD` の前提）。 -/
theorem write_head_after (ge : CGenv) (hcenv : ge.genv_cenv = Deb2025_10148_deb_after.prog.prog_comp_env)
    (c : Ctx) (errB : Block) (rb : List MemVal) (X : ExtD ge c.encB rb)
    (hpl : Integers.Int64.lt c.pl (Integers.Int64.repr 0) = false)
    (hrem : Integers.Int64.lt (Integers.Int64.repr 0) c.rem = false)
    (hdata : IsPtr c.dataV) (hout : IsPtr c.outV) (hm0 : c.m0.length = 4) (hrb : rb.length = 4)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal FD1) (specDA c errB) vs := by
  have hcenv' := hcenv.trans cenv_deb_after_same
  by_cases hvs : vs = [c.dataV, .Vptr c.encB Integers.Ptrofs.zero, .Vint c.fl, .Vlong c.pl, c.outV,
      .Vptr errB Integers.Ptrofs.zero]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := write_head_after_entry_wf
  refine satisfies_internal ge (FunctionEntry2 ge) FD1 _ _
    (fun e le hp => ∃ hb, P0D c errB hb e le hp)
    (fun m hp hf hpre hd hag => ?_)
    (triple_lift ge _ _ _ _ _ _ (fun e le hp h => h) (fun hb =>
      body_dafter ge hcenv' c rb X hpl hrem hdata hout hm0 hrb errB hb))
  let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv (tarray tuchar 14))
  have hav : AllocVariables ge.genv_cenv emptyEnv m FD1.fn_vars (envD a1.2) a1.1 :=
    .cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _)
  obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav hnv
    (by
      intro v hv
      simp only [FD1, Deb2025_10148_deb_after.f_ws_enc_write_head, List.mem_cons, List.mem_nil_iff,
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
        (createUndefTemps FD1.fn_temps)))))),
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

end Deb2025_10148C
