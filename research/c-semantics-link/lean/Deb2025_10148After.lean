/-
CVE-2025-10148: 上流の修正後（84db7a9eae）の `ws_enc_add_frame`（U1）。

証明すること（`add_frame_after`、P1）: `Curl_bufq_write` に渡すヘッダ（局所変数 `head` の先頭 `hlen` バイト）の最後の4バイトは、
この呼び出しの中で `Curl_rand` が `enc->mask` に書いた4バイト `rb` である。
`Curl_bufq_write` の仕様（`bufqSpec`）の前提にそれを書き、その仮定のもとで関数の仕様を証明する。`rb` は任意。
-/
import Deb2025_10148Common
open CC CC.Sep CC.HProp
open Deb2025_10148_up_after
open Case5C (RR boolVal_ofBool_tint)
open Case4debC (IsPtr cast_ptr)
open Deb2026_3805C (call2 set2 call_none heap_eq heap_imp triple_lift temps_weak once_loop int_eq_false ex_map)

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Deb2025_10148C

/-! ## 入口の状態 -/

/-- 関数の引数と、`enc` の指す構造体の入口の中身。 -/
structure Ctx where
  dataV : Val                -- data（外部関数に渡すだけ）
  encB : Block               -- enc（ブロックの先頭を指す）
  fl : Integers.Int          -- flags
  pl : Integers.Int64        -- payload_len
  outV : Val                 -- out（外部関数に渡すだけ）
  rem : Integers.Int64       -- 入口の enc->payload_remain
  w : Integers.Int           -- 入口の、オフセット 24 の 32 bit（firstbyte と contfragment）
  m0 : List MemVal           -- 入口の enc->mask（4バイト）

abbrev AB (b : Block) (o : Z) (n : Nat) : HProp := anyBytes .Freeable b o n

/-- 入口の `*enc`: `payload_len`（書くだけ）、`payload_remain`（読む）、`xori`（書くだけ）、`mask`（4バイト `m0`）、
    オフセット 24 の 32 bit（`contfragment` を読み書きする）。 -/
def encPre (c : Ctx) : HProp :=
  AB c.encB 0 8 ∗ mapsto .Mint64 .Freeable c.encB 8 (.Vlong c.rem) ∗ AB c.encB 16 4
  ∗ bytesPtsTo c.encB .Freeable 20 c.m0 ∗ mapsto .Mint32 .Freeable c.encB 24 (.Vint c.w)

/-- 出口の `*enc`。`mask` の4バイトは `mk` で与える。 -/
def encPost (b : Block) (mk : HProp) : HProp :=
  AB b 0 8 ∗ AB b 8 8 ∗ AB b 16 4 ∗ mk ∗ AB b 24 4

/-- 局所変数 `firstb`・`head`・`nwritten`。 -/
abbrev LU (fbB hb nwB : Block) : HProp := AB fbB 0 1 ∗ AB hb 0 14 ∗ AB nwB 0 8

theorem locs_LU (fbB hb nwB : Block) :
    Case3C.Locs [(fbB, 1), (hb, 14), (nwB, 8)] = LU fbB hb nwB := by
  simp only [Case3C.Locs, sep_emp_eq]

def envU (fbB hb nwB : Block) : Env :=
  ((emptyEnv.set _firstb (fbB, tuchar)).set _head (hb, tarray tuchar 14)).set _nwritten (nwB, tulong)

theorem blocks_envU (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (fbB hb nwB : Block) :
    blocksOfEnv ge.genv_cenv (envU fbB hb nwB) = [(hb, 0, 14), (fbB, 0, 1), (nwB, 0, 8)] := by
  rw [hcenv]; rfl

theorem envU_fb (fbB hb nwB : Block) : (envU fbB hb nwB).get _firstb = some (fbB, tuchar) := rfl
theorem envU_head (fbB hb nwB : Block) : (envU fbB hb nwB).get _head = some (hb, tarray tuchar 14) := rfl
theorem envU_nw (fbB hb nwB : Block) : (envU fbB hb nwB).get _nwritten = some (nwB, tulong) := rfl

/-! ## 外部関数の仕様（弱く書く） -/

abbrev easyT : Ty := Ty.Tstruct _Curl_easy noattr
abbrev ccVar : CallConv := { cc_vararg := some 2, cc_unproto := false, cc_structret := false }

/-- `Curl_failf(data, fmt)`（可変長引数）: 何もしない。 -/
def failSpec : FunSpec where
  tyargs := [tptr easyT, tptr tschar]
  tyres := tvoid
  cc := ccVar
  pre := fun _ hp => emp hp
  post := fun _ hp => emp hp
  measure := fun _ => 0

/-- `ws_frame_flags2firstbyte(data, flags, contfragment, &firstb)`: 何かのコードを返す。CURLE_OK のときは `firstb` に何かの1バイトを書く。 -/
def fbSpec (fbB : Block) : FunSpec where
  tyargs := [tptr easyT, tuint, tbool, tptr tuchar]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => (∃ a b c, vargs = [a, b, c, .Vptr fbB Integers.Ptrofs.zero]) ∧ AB fbB 0 1 hp
  post := fun v hp => ∃ r, v = .Vint r ∧ AB fbB 0 1 hp
    ∧ (r = Integers.Int.zero → ∃ x, mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) hp)
  measure := fun _ => 0

/-- `ws_enc_info(enc, data, "sending")`（ログを書くだけ）: 何もしない。 -/
def infoSpec : FunSpec where
  tyargs := [tptr encT, tptr easyT, tptr tschar]
  tyres := tvoid
  cc := cc_default
  pre := fun _ hp => emp hp
  post := fun _ hp => emp hp
  measure := fun _ => 0

/-- `Curl_rand(data, enc->mask, 4)`（`Curl_rand_bytes`）: 失敗のコードか、CURLE_OK を返して `enc->mask` に4バイト `rb` を書く。 -/
def randSpec (encB : Block) (rb : List MemVal) : FunSpec where
  tyargs := [tptr easyT, tptr tuchar, tulong]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => (∃ a o, Integers.Ptrofs.unsigned o = 20
      ∧ vargs = [a, .Vptr encB o, .Vlong (Integers.Int64.repr 4)]) ∧ AB encB 20 4 hp
  post := fun v hp => ∃ r, v = .Vint r
    ∧ ((r = Integers.Int.zero ∧ bytesPtsTo encB .Freeable 20 rb hp) ∨ (r ≠ Integers.Int.zero ∧ AB encB 20 4 hp))
  measure := fun _ => 0

/-- `memcpy(&head[n], enc->mask, 4)`: `enc->mask` の4バイト `mb` を `head` の `n` から写す。 -/
def cpySpec (hb : Block) (n : Nat) (encB : Block) (mb : List MemVal) : FunSpec where
  tyargs := [tptr tvoid, tptr tvoid, tulong]
  tyres := tptr tvoid
  cc := cc_default
  pre := fun vargs hp => (∃ o1 o2, Integers.Ptrofs.unsigned o1 = n ∧ Integers.Ptrofs.unsigned o2 = 20
      ∧ vargs = [.Vptr hb o1, .Vptr encB o2, .Vlong (Integers.Int64.repr 4)])
    ∧ (AB hb n 4 ∗ bytesPtsTo encB .Freeable 20 mb) hp
  post := fun _ hp => (bytesPtsTo hb .Freeable n mb ∗ bytesPtsTo encB .Freeable 20 mb) hp
  measure := fun _ => 0

/-- `Curl_bufq_write(out, head, n + 4, &nwritten)`。**前提に P1 を書く**: 渡すヘッダ `head[0 .. n+4)` の最後の4バイト
    （`head[n .. n+4)`）が `mb`。何かのコードを返し、`nwritten` に何かの長さを書く。 -/
def bufqSpec (hb : Block) (n : Nat) (mb : List MemVal) (nwB : Block) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _bufq noattr), tptr tuchar, tulong, tptr tulong]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => (∃ a, vargs = [a, .Vptr hb Integers.Ptrofs.zero,
      .Vlong (Integers.Int64.repr ((n : Z) + 4)), .Vptr nwB Integers.Ptrofs.zero])
    ∧ (AB hb 0 n ∗ bytesPtsTo hb .Freeable n mb ∗ AB hb ((n : Z) + 4) (10 - n) ∗ AB nwB 0 8) hp
  post := fun v hp => ∃ r k, v = .Vint r
    ∧ (AB hb 0 14 ∗ mapsto .Mint64 .Freeable nwB 0 (.Vlong k)) hp
  measure := fun _ => 0

/-- 呼ばれる側の関数（記号・型・仕様）。`rb` は `Curl_rand` が書く4バイト。 -/
structure Ext (ge : CGenv) (encB : Block) (rb : List MemVal) : Prop where
  fail : ∃ b fd, Genv.findSymbol ge.genv_genv _Curl_failf = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr easyT, tptr tschar] tvoid ccVar
    ∧ ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fd failSpec vs
  fb : ∃ b fd, Genv.findSymbol ge.genv_genv _ws_frame_flags2firstbyte = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr easyT, tuint, tbool, tptr tuchar] tint cc_default
    ∧ ∀ fbB vs, SatisfiesAt ge (FunctionEntry2 ge) fd (fbSpec fbB) vs
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
    ∧ typeOfFundef fd = .Tfunction [tptr (Ty.Tstruct _bufq noattr), tptr tuchar, tulong, tptr tulong] tint cc_default
    ∧ ∀ hb n nwB vs, SatisfiesAt ge (FunctionEntry2 ge) fd (bufqSpec hb n rb nwB) vs
  lit3 : ∃ b, Genv.findSymbol ge.genv_genv ___stringlit_3 = some b
  lit4 : ∃ b, Genv.findSymbol ge.genv_genv ___stringlit_4 = some b
  lit5 : ∃ b, Genv.findSymbol ge.genv_genv ___stringlit_5 = some b
  lit6 : ∃ b, Genv.findSymbol ge.genv_genv ___stringlit_6 = some b

/-! ## 事後条件と return -/

/-- 事後条件（U1）: `*enc` の所有を返す（`mask` は中身を問わない）。戻り値は問わない。 -/
def postA (c : Ctx) : Val → HProp := fun _ hp => encPost c.encB (AB c.encB 20 4) hp

abbrev F1 : Function := f_ws_enc_add_frame
abbrev B1 : Stmt := f_ws_enc_add_frame.fn_body

/-- 局所変数を手放して return する。 -/
theorem retU (ge : CGenv) (fe) (hcenv : ge.genv_cenv = prog.prog_comp_env) (fbB hb nwB : Block)
    (hne : fbB ≠ hb ∧ fbB ≠ nwB ∧ hb ≠ nwB)
    (l : List (Ident × Val)) (Hk : HProp) (a : Expr) (v : Val) (Ret : Val → HProp) (Q : Sep.Assn)
    (hev : ∀ le m, TempsHold l le → EvalExpr ge (envU fbB hb nwB) le m a v)
    (hcast : ∀ m, Cop.semCast v (typeof a) F1.fn_return m = some v)
    (hret : ∀ hp, Hk hp → Ret v hp) :
    Triple ge fe F1 (LocalSt (envU fbB hb nwB) l (Hk ∗ LU fbB hb nwB)) (.Sreturn (some a)) (RR Ret Q) := by
  rw [← locs_LU]
  refine triple_conseq ge fe F1
    (Case3C.ret_locs ge fe F1 (envU fbB hb nwB) l Hk [(fbB, 1), (hb, 14), (nwB, 8)] a v v Ret
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

/-! ## 本体の文（`sp i B1` の先頭）ごとの証明 -/

/-- 引数の並び（`Lk`）。 -/
abbrev Lk (c : Ctx) : List (Ident × Val) :=
  [(_out, c.outV), (_payload_len, .Vlong c.pl), (_flags, .Vint c.fl),
   (_enc, .Vptr c.encB Integers.Ptrofs.zero), (_data, c.dataV)]

/-- `int` から `_Bool` への変換の結果。 -/
def boolOf : Val → Val
  | .Vint x => .Vint (if Integers.Int.eq x Integers.Int.zero then Integers.Int.zero else Integers.Int.one)
  | v => v

/-- `contfragment` を読んだ値。 -/
def cfV (c : Ctx) : Val := .Vint (Cop.bitfieldExtract .I32 .Unsigned 8 1 c.w)

abbrev L4 (c : Ctx) (v : Val) : List (Ident × Val) :=
  (_result, v) :: (_t'1, v) :: (_t'12, cfV c) :: (_t'13, .Vlong c.rem) :: Lk c

abbrev L13 (c : Ctx) (n : Nat) : List (Ident × Val) :=
  (_hlen, .Vlong (Integers.Int64.repr n)) :: Lk c

abbrev L16 (c : Ctx) (n : Nat) : List (Ident × Val) :=
  (_hlen, .Vlong (Integers.Int64.repr ((n : Z) + 4))) :: Lk c

/-- `*enc` の途中の形。`mk` は mask、`wd` はオフセット 24 の4バイト。 -/
abbrev encA (b : Block) (mk wd : HProp) : HProp := AB b 0 8 ∗ AB b 8 8 ∗ AB b 16 4 ∗ mk ∗ wd

abbrev mk0 (c : Ctx) : HProp := bytesPtsTo c.encB .Freeable 20 c.m0
abbrev wd32 (c : Ctx) (w : Integers.Int) : HProp := mapsto .Mint32 .Freeable c.encB 24 (.Vint w)

abbrev K4 (c : Ctx) (hb nwB : Block) : HProp :=
  AB hb 0 14 ∗ AB nwB 0 8 ∗ encA c.encB (mk0 c) (wd32 c c.w)

abbrev K6 (c : Ctx) (hb nwB : Block) : HProp :=
  AB hb 0 14 ∗ AB nwB 0 8 ∗ encA c.encB (mk0 c) (AB c.encB 24 4)
abbrev K10 (c : Ctx) : HProp := encA c.encB (mk0 c) (AB c.encB 24 4)
abbrev K13 (c : Ctx) (fbB hb nwB : Block) : HProp :=
  LU fbB hb nwB ∗ AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ AB c.encB 24 4
/-- memcpy のあと: `head[n .. n+4)` と `enc->mask` がどちらも `rb`。 -/
abbrev K15 (c : Ctx) (fbB hb nwB : Block) (n : Nat) : HProp :=
  AB hb 0 n ∗ AB hb ((n : Z) + 4) (10 - n) ∗ AB fbB 0 1 ∗ AB nwB 0 8
  ∗ AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ AB c.encB 24 4
abbrev K18 (c : Ctx) (fbB : Block) (rb : List MemVal) : HProp :=
  AB fbB 0 1 ∗ bytesPtsTo c.encB .Freeable 20 rb ∗ AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ AB c.encB 24 4

macro "acx" : tactic => `(tactic| (
  (try simp only [Deb2025_10148C.encPre, Deb2025_10148C.encA, Deb2025_10148C.LU, Deb2025_10148C.mk0,
    Deb2025_10148C.wd32, Deb2025_10148C.K4, Deb2025_10148C.K6, Deb2025_10148C.K10, Deb2025_10148C.K13, Deb2025_10148C.K15, Deb2025_10148C.K18, Deb2025_10148C.encPost]) <;> ac_rfl))

macro "unf" : tactic => `(tactic| (conv => arg 5; dsimp only [Deb2025_10148C.hdS, Deb2025_10148C.sp,
  Deb2025_10148C.B1, Deb2025_10148_up_after.f_ws_enc_add_frame]))

macro "lm" : tactic => `(tactic| (
  try dsimp only [Deb2025_10148C.Lk, Deb2025_10148C.L4, Deb2025_10148C.L13, Deb2025_10148C.L16]
  repeat (first | exact List.mem_cons_self .. | apply List.mem_cons_of_mem)))

macro "lf" : tactic => `(tactic| (
  try dsimp only [Deb2025_10148C.Lk, Deb2025_10148C.L4, Deb2025_10148C.L13, Deb2025_10148C.L16]
  repeat' (first | exact fun _ h => absurd h List.not_mem_nil | refine List.forall_mem_cons.mpr ⟨?_, ?_⟩)
  all_goals (try dsimp only)
  all_goals decide))

macro "ls" : tactic => `(tactic| (
  try dsimp only [Deb2025_10148C.Lk, Deb2025_10148C.L4, Deb2025_10148C.L13, Deb2025_10148C.L16]
  repeat' (first | exact fun _ h => absurd h List.not_mem_nil | refine List.forall_mem_cons.mpr ⟨?_, ?_⟩)
  all_goals lm))

syntax "evx" : tactic
macro_rules
  | `(tactic| evx) => `(tactic| first
      | exact EvalExpr.Econst_int _ _
      | exact EvalExpr.Etempvar _ _ _ ((‹TempsHold _ _›).get (by lm))
      | (refine EvalExpr.Ecast _ _ ?_ ?_ ?_ ?_; all_goals first | evx | rfl | skip)
      | (refine EvalExpr.Ebinop _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_; all_goals first | evx | rfl | skip)
      | (refine EvalExpr.Eunop _ _ _ ?_ ?_ ?_ ?_; all_goals first | evx | rfl | skip))

macro "eargs" : tactic => `(tactic| (
  repeat' (first | exact EvalExprlist.nil | refine EvalExprlist.cons _ _ _ _ ?_ _ _ ?_ ?_ ?_)
  all_goals (first
    | exact EvalExpr.Etempvar _ _ _ ((‹TempsHold _ _›).get (by lm))
    | exact EvalExpr.Econst_int _ _
    | exact EvalExpr.Eaddrof _ _ _ _ (eval_var_local (Deb2025_10148C.envU_fb _ _ _))
    | exact EvalExpr.Eaddrof _ _ _ _ (eval_var_local (Deb2025_10148C.envU_nw _ _ _))
    | exact cast_ptr ‹IsPtr _› _ _ _
    | rfl
    | skip)))

theorem cell_ld {H R : HProp} {chunk : Chunk} {b : Block} {o : Z} {v : Val} {hp : Heap} {m : Mem}
    (heq : H = mapsto chunk .Freeable b o v ∗ R) (hH : H hp) (hag : Heap.Agrees hp m) :
    Mem.load chunk m b o = some (Val.loadResult chunk v) := by
  rw [heq] at hH
  obtain ⟨h1, h2, _, rfl, hm, _⟩ := hH
  exact mapsto_load (by decide) hm (Heap.Agrees_union_left hag)

theorem mk_any {b : Block} {l : List MemVal} {h : Heap} (hl : l.length = 4)
    (hb : bytesPtsTo b .Freeable 20 l h) : AB b 20 4 h := bytes_anyB hl hb

/-- 前の段の所有から事後条件へ。 -/
theorem post_A (c : Ctx) (hm0 : c.m0.length = 4) (wd : HProp) (hwd : ∀ h, wd h → AB c.encB 24 4 h)
    (v : Val) (hp : Heap) (h : encA c.encB (mk0 c) wd hp) : postA c v hp := by
  obtain ⟨h1, r1, d1, e1, a1, h2⟩ := h
  obtain ⟨h3, r3, d3, e3, a3, h4⟩ := h2
  obtain ⟨h5, r5, d5, e5, a5, h6⟩ := h4
  obtain ⟨h7, r7, d7, e7, a7, a8⟩ := h6
  exact ⟨h1, r1, d1, e1, a1, h3, r3, d3, e3, a3, h5, r5, d5, e5, a5, h7, r7, d7, e7,
    mk_any hm0 a7, hwd _ a8⟩

theorem conv1 {P P' R G : HProp} {hp : Heap} (hi : ∀ h, P h → P' h) (heq : P' ∗ R = G)
    (hs : (P ∗ R) hp) : G hp := heq ▸ sep_imp_l hi hs

/-- 前提の純粋な条件を取り出す。 -/
theorem pure_l (ge fe f) (φ : Prop) (P : Sep.Assn) (s : Stmt) (R : Sep.ExitConds)
    (h : φ → Triple ge fe f P s R) : Triple ge fe f (fun e le hp => φ ∧ P e le hp) s R := by
  intro k e le hp hf m hd hag ⟨hφ, hP⟩
  exact h hφ k e le hp hf m hd hag hP

/-- `if (a) s1 else s2` で、条件の値が分からないときは両方の枝を示す。 -/
theorem if_both (ge fe f) (E : Env) (l : List (Ident × Val)) (H : HProp) (a : Expr) (s1 s2 : Stmt)
    (R : Sep.ExitConds)
    (hg : ∀ le m, TempsHold l le → ∃ v b, EvalExpr ge E le m a v ∧ Cop.boolVal v (typeof a) m = some b)
    (h1 : Triple ge fe f (LocalSt E l H) s1 R) (h2 : Triple ge fe f (LocalSt E l H) s2 R) :
    Triple ge fe f (LocalSt E l H) (.Sifthenelse a s1 s2) R := by
  refine triple_if ge fe f _ _ _ R a s1 s2 (fun e le hp m hP _ => ?_) h1 h2
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  obtain ⟨v, b, hev, hb⟩ := hg le m hT
  exact ⟨v, b, hev, hb, by cases b <;> exact ⟨rfl, hT, hH⟩⟩

/-- `.only` の結果を、次の段の前提に言い換える。 -/
theorem post_to (ge fe f) {P Q Q' : Sep.Assn} {s : Stmt} (Ret : Val → HProp)
    (h : Triple ge fe f P s (.only Q)) (hq : ∀ e le hp, Q e le hp → Q' e le hp) :
    Triple ge fe f P s (RR Ret Q') :=
  triple_conseq ge fe f h (fun _ _ _ x => x) hq (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim)
    (fun _ _ x => x.elim)

theorem cast_bool_ofBool (b : Bool) (m : Mem) : Cop.semCast (Val.ofBool b) tint tbool m = some (Val.ofBool b) := by
  cases b <;> rfl

theorem emp_l (H : HProp) : H = emp ∗ H := (emp_sep_eq H).symm

/-- 一時変数への代入（値は存在で持つ）。 -/
theorem set_ex (ge fe f) (E : Env) (l : List (Ident × Val)) (H : HProp) (id : Ident) (a : Expr)
    (hne : ∀ q ∈ l, q.1 ≠ id)
    (hev : ∀ le m hp, TempsHold l le → H hp → Heap.Agrees hp m → ∃ v, EvalExpr ge E le m a v) :
    Triple ge fe f (LocalSt E l H) (.Sset id a)
      (.only (fun e le hp => ∃ v, LocalSt E ((id, v) :: l) H e le hp)) := by
  refine triple_set ge fe f _ _ id a (fun e le hp m hP hag => ?_)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  obtain ⟨v, hv⟩ := hev le m hp hT hH hag
  exact ⟨v, hv, v, rfl, TempsHold_set hne hT, hH⟩

/-- `head[k]`（`head` は局所変数の配列）。 -/
theorem lv_head {ge : CGenv} {E : Env} {le : TempEnv} {m : Mem} {hb : Block} (k : Z)
    (hE : E.get _head = some (hb, tarray tuchar 14)) :
    EvalLvalue ge E le m (.Ederef (.Ebinop .Oadd (.Evar _head (tarray tuchar 14))
      (.Econst_int (Integers.Int.repr k) tint) (tptr tuchar)) tuchar) hb
      (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.mul (Integers.Ptrofs.repr (sizeof ge.genv_cenv tuchar))
        (Cop.ptrofsOfInt .Signed (Integers.Int.repr k)))) .Full :=
  EvalLvalue.Ederef _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _
    (EvalExpr.Elvalue _ _ _ _ _ (eval_var_local hE) (DerefLoc.reference rfl)) (EvalExpr.Econst_int _ _)
    (semAdd_ptr_int _ _ _ _ _ rfl))

/-- `head[k] = a2;`（`head` は中身を問わない 14 バイトとして持つ）。 -/
theorem hstore (ge fe f) (E : Env) (l : List (Ident × Val)) (H : HProp) (hb : Block)
    (hE : E.get _head = some (hb, tarray tuchar 14)) (k r : Nat) (hk : k + (1 + r) = 14) (a2 : Expr)
    (ho : Integers.Ptrofs.unsigned (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.mul
      (Integers.Ptrofs.repr (sizeof ge.genv_cenv tuchar)) (Cop.ptrofsOfInt .Signed (Integers.Int.repr k)))) = 0 + k)
    (hev : ∀ le m, TempsHold l le →
      ∃ v2 vnew, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) tuchar m = some vnew) :
    Triple ge fe f (LocalSt E l (AB hb 0 14 ∗ H))
      (.Sassign (.Ederef (.Ebinop .Oadd (.Evar _head (tarray tuchar 14))
        (.Econst_int (Integers.Int.repr k) tint) (tptr tuchar)) tuchar) a2)
      (.only (LocalSt E l (AB hb 0 14 ∗ H))) := by
  have := store_byte ge fe f E l H _ a2 hb _ 0 k r rfl ho (fun le m _ => lv_head k hE) hev
  rw [hk] at this
  exact this

/-- 本体の 10 番目の文（ヘッダの組み立て。`payload_len` で3つに分かれる）。U1・U0・D1・D0 で同じ文。 -/
theorem hdr (ge fe f) (E : Env) (l' : List (Ident × Val)) (pl : Integers.Int64) (H : HProp)
    (Ret : Val → HProp) (hb : Block) (hE : E.get _head = some (hb, tarray tuchar 14))
    (hfr : ∀ q ∈ (_payload_len, Val.Vlong pl) :: l', q.1 ≠ _hlen) :
    Triple ge fe f (LocalSt E ((_payload_len, .Vlong pl) :: l') (AB hb 0 14 ∗ H)) (hdS (sp 10 B1))
      (RR Ret (fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
        ∧ LocalSt E ((_hlen, .Vlong (Integers.Int64.repr n)) :: (_payload_len, .Vlong pl) :: l')
          (AB hb 0 14 ∗ H) e le hp)) := by
  unf
  refine if_both ge _ _ _ _ _ _ _ _ _ (fun le m hT =>
    ⟨Val.ofBool (Integers.Int64.lt (Integers.Int64.repr (Integers.Int.signed (Integers.Int.repr 65535))) pl), _,
      EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..)))
        (EvalExpr.Econst_int _ _) rfl, boolVal_ofBool_tint _ _⟩) ?_ ?_
  · refine triple_seq_fwd ge _ _ _ _ _ _ _ (hstore ge _ _ _ _ _ hb hE 1 12 rfl _ rfl
      (fun le m hT => ⟨_, _, by evx, rfl⟩)) ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (hstore ge _ _ _ _ _ hb hE 2 11 rfl _ rfl
      (fun le m hT => ⟨_, _, by evx, rfl⟩)) ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (hstore ge _ _ _ _ _ hb hE 3 10 rfl _ rfl
      (fun le m hT => ⟨_, _, by evx, rfl⟩)) ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (hstore ge _ _ _ _ _ hb hE 4 9 rfl _ rfl
      (fun le m hT => ⟨_, _, by evx, rfl⟩)) ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (hstore ge _ _ _ _ _ hb hE 5 8 rfl _ rfl
      (fun le m hT => ⟨_, _, by evx, rfl⟩)) ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (hstore ge _ _ _ _ _ hb hE 6 7 rfl _ rfl
      (fun le m hT => ⟨_, _, by evx, rfl⟩)) ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (hstore ge _ _ _ _ _ hb hE 7 6 rfl _ rfl
      (fun le m hT => ⟨_, _, by evx, rfl⟩)) ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (hstore ge _ _ _ _ _ hb hE 8 5 rfl _ rfl
      (fun le m hT => ⟨_, _, by evx, rfl⟩)) ?_
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (hstore ge _ _ _ _ _ hb hE 9 4 rfl _ rfl
      (fun le m hT => ⟨_, _, by evx, rfl⟩)) ?_
    refine post_to ge _ _ _ (set2 ge _ _ _ _ _ _hlen _ (.Vlong (Integers.Int64.repr 10)) hfr
      (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)) ?_
    exact fun e le hp h => ⟨10, Or.inr (Or.inr rfl), h⟩
  · refine if_both ge _ _ _ _ _ _ _ _ _ (fun le m hT =>
      ⟨Val.ofBool (!Integers.Int64.lt pl (Integers.Int64.repr (Integers.Int.signed (Integers.Int.repr 126)))), _,
        EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..)))
          (EvalExpr.Econst_int _ _) rfl, boolVal_ofBool_tint _ _⟩) ?_ ?_
    · refine triple_seq_fwd ge _ _ _ _ _ _ _ (hstore ge _ _ _ _ _ hb hE 1 12 rfl _ rfl
        (fun le m hT => ⟨_, _, by evx, rfl⟩)) ?_
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (hstore ge _ _ _ _ _ hb hE 2 11 rfl _ rfl
        (fun le m hT => ⟨_, _, by evx, rfl⟩)) ?_
      refine triple_seq_fwd ge _ _ _ _ _ _ _ (hstore ge _ _ _ _ _ hb hE 3 10 rfl _ rfl
        (fun le m hT => ⟨_, _, by evx, rfl⟩)) ?_
      refine post_to ge _ _ _ (set2 ge _ _ _ _ _ _hlen _ (.Vlong (Integers.Int64.repr 4)) hfr
        (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)) ?_
      exact fun e le hp h => ⟨4, Or.inr (Or.inl rfl), h⟩
    · refine triple_seq_fwd ge _ _ _ _ _ _ _ (hstore ge _ _ _ _ _ hb hE 1 12 rfl _ rfl
        (fun le m hT => ⟨_, _, by evx, rfl⟩)) ?_
      refine post_to ge _ _ _ (set2 ge _ _ _ _ _ _hlen _ (.Vlong (Integers.Int64.repr 2)) hfr
        (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)) ?_
      exact fun e le hp h => ⟨2, Or.inl rfl, h⟩

/-- 呼び出し（戻り値を捨てる）。引数の値は状態ごとに存在で与え、事後条件の所有を残す。 -/
theorem call_none_ex (ge fe f) (S : FunSpec) (a : Expr) (al : List Expr)
    (E : Env) (l : List (Ident × Val)) (Hpre Hkeep : HProp) (fb : Block) (fd : FunDef)
    (hspec : ∀ vs, SatisfiesAt ge fe fd S vs) (hfind : FuncPtr ge fb fd)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun (typeof a) = .f S.tyargs S.tyres S.cc)
    (hcallee : ∀ le m, TempsHold l le → EvalExpr ge E le m a (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le →
      ∃ vargs, EvalExprlist ge E le m al S.tyargs vargs ∧ ∀ h, Hpre h → S.pre vargs h) :
    Triple ge fe f (LocalSt E l (Hpre ∗ Hkeep)) (.Scall none a al)
      (.only (fun e le hp => ∃ v, LocalSt E l (S.post v ∗ Hkeep) e le hp)) := by
  refine triple_call ge fe f S none a al _ _ fb fd hspec hfind hty hclass
    (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, h1, h2, hd, heq, hH1, hH2⟩ := hP
  subst he
  obtain ⟨vargs, hev, hpre⟩ := hargs le m hT
  exact ⟨vargs, h1, h2, hd, heq, hcallee le m hT, hev, hpre h1 hH1,
    fun v h1' hS hd' => ⟨v, rfl, hT, h1', h2, hd', rfl, hS, hH2⟩⟩

/-- 前提の「または」を枝に分ける。 -/
theorem or_l (ge fe f) (A B : Sep.Assn) (s : Stmt) (R : Sep.ExitConds)
    (ha : Triple ge fe f A s R) (hb : Triple ge fe f B s R) :
    Triple ge fe f (fun e le hp => A e le hp ∨ B e le hp) s R := by
  intro k e le hp hf m hd hag hP
  rcases hP with h | h
  · exact ha k e le hp hf m hd hag h
  · exact hb k e le hp hf m hd hag h

/-- `head` の 14 バイトを、`n` からの4バイトとその前後に分ける。 -/
theorem head_split (hb : Block) (n : Nat) (hn : n ≤ 10) :
    AB hb 0 14 = AB hb n 4 ∗ (AB hb 0 n ∗ AB hb ((n : Z) + 4) (10 - n)) := by
  have := any3 hb 0 n 4 (10 - n)
  rw [show n + (4 + (10 - n)) = 14 by omega, Int.zero_add] at this
  exact this

theorem hn_le {n : Nat} (hn : n = 2 ∨ n = 4 ∨ n = 10) : n ≤ 10 := by omega

section
variable (ge : CGenv) (c : Ctx) (fbB hb nwB : Block)

abbrev EU := envU fbB hb nwB

def P0 : Sep.Assn := LocalSt (envU fbB hb nwB) (Lk c) (encPre c ∗ LU fbB hb nwB)

theorem s0 : Triple ge (FunctionEntry2 ge) F1 (P0 c fbB hb nwB) (hdS (sp 0 B1))
    (RR (postA c) (P0 c fbB hb nwB)) := by
  refine only_RR _ _ _ _ ?_
  show Sep.Triple _ _ _ _ (.Sassign (.Evar _firstb tuchar) (.Econst_int (Integers.Int.repr 0) tint)) _
  unfold P0
  have he : encPre c ∗ LU fbB hb nwB = AB fbB 0 1 ∗ (encPre c ∗ AB hb 0 14 ∗ AB nwB 0 8) := by
    unfold LU; acx
  rw [he]
  exact store_any ge _ _ _ _ _ _ _ .Mint8unsigned fbB Integers.Ptrofs.zero 0 rfl rfl rfl
    (fun _ _ _ => eval_var_local (envU_fb _ _ _)) (fun _ _ _ => ⟨_, _, EvalExpr.Econst_int _ _, rfl⟩)

theorem s1 (hpl : Integers.Int64.lt c.pl (Integers.Int64.repr 0) = false) :
    Triple ge (FunctionEntry2 ge) F1 (P0 c fbB hb nwB) (hdS (sp 1 B1))
      (RR (postA c) (P0 c fbB hb nwB)) := by
  unf
  unfold P0
  refine if_val ge _ _ _ _ _ _ false _ _ _ (Val.ofBool false) ?_ (fun m => boolVal_ofBool_tint _ m) ?_
  · intro le m hp hT _ _
    refine EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lm)))
      (EvalExpr.Econst_int _ _) ?_
    show some (Val.ofBool (Integers.Int64.lt c.pl (Integers.Int64.repr 0))) = _
    rw [hpl]
  · exact skip_to ge _ _ _ _ _ (fun _ _ _ x => x)

def P3 : Sep.Assn := LocalSt (envU fbB hb nwB) ((_t'13, .Vlong c.rem) :: Lk c)
  (encA c.encB (mk0 c) (wd32 c c.w) ∗ LU fbB hb nwB)

theorem s2 (hcenv : ge.genv_cenv = prog.prog_comp_env) (hrem : Integers.Int64.lt (Integers.Int64.repr 0) c.rem = false) :
    Triple ge (FunctionEntry2 ge) F1 (P0 c fbB hb nwB) (hdS (sp 2 B1))
      (RR (postA c) (P3 c fbB hb nwB)) := by
  unf
  unfold P0
  have he : encPre c ∗ LU fbB hb nwB = mapsto .Mint64 .Freeable c.encB 8 (.Vlong c.rem)
      ∗ (AB c.encB 0 8 ∗ AB c.encB 16 4 ∗ mk0 c ∗ wd32 c c.w ∗ LU fbB hb nwB) := by
    unfold encPre; acx
  refine triple_seq_fwd ge _ _ _
    (LocalSt (envU fbB hb nwB) ((_t'13, .Vlong c.rem) :: Lk c) (encPre c ∗ LU fbB hb nwB)) _ _ _ ?_ ?_
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
      exact conv1 (P' := AB c.encB 8 8) (fun _ x => mapsto_anyB x) (by acx) hH


def P4 : Sep.Assn := fun e le hp => ∃ v,
  LocalSt (envU fbB hb nwB) (L4 c v) ((fbSpec fbB).post v ∗ K4 c hb nwB) e le hp

theorem s3 (hcenv : ge.genv_cenv = prog.prog_comp_env) (rb : List MemVal) (X : Ext ge c.encB rb) (hdata : IsPtr c.dataV) :
    Triple ge (FunctionEntry2 ge) F1 (P3 c fbB hb nwB) (hdS (sp 3 B1))
      (RR (postA c) (P4 c fbB hb nwB)) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.fb
  refine only_RR _ _ _ _ ?_
  unf
  unfold P3
  have hw : encA c.encB (mk0 c) (wd32 c c.w) ∗ LU fbB hb nwB = wd32 c c.w
      ∗ (AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ mk0 c ∗ LU fbB hb nwB) := by acx
  have hf : encA c.encB (mk0 c) (wd32 c c.w) ∗ LU fbB hb nwB = AB fbB 0 1 ∗ K4 c hb nwB := by
    acx
  refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ v, LocalSt (envU fbB hb nwB)
      ((_t'1, v) :: (_t'12, cfV c) :: (_t'13, .Vlong c.rem) :: Lk c)
      ((fbSpec fbB).post v ∗ K4 c hb nwB) e le hp) _ _ _ ?_ ?_
  · refine triple_seq_fwd ge _ _ _ (LocalSt (envU fbB hb nwB)
      ((_t'12, cfV c) :: (_t'13, .Vlong c.rem) :: Lk c)
      (encA c.encB (mk0 c) (wd32 c c.w) ∗ LU fbB hb nwB)) _ _ _ ?_ ?_
    · refine set2 ge _ _ _ _ _ _t'12 _ (cfV c) (by lf) ?_
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

def P5 : Sep.Assn := fun e le hp => ∃ x, LocalSt (envU fbB hb nwB) (L4 c (.Vint Integers.Int.zero))
  (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K4 c hb nwB) e le hp

theorem s4 (hcenv : ge.genv_cenv = prog.prog_comp_env) (hm0 : c.m0.length = 4) (hne : fbB ≠ hb ∧ fbB ≠ nwB ∧ hb ≠ nwB) :
    Triple ge (FunctionEntry2 ge) F1 (P4 c fbB hb nwB) (hdS (sp 4 B1))
      (RR (postA c) (P5 c fbB hb nwB)) := by
  unf
  refine triple_lift ge _ _ (fun x : Val × Integers.Int => fun e le hp => x.1 = .Vint x.2
      ∧ LocalSt (envU fbB hb nwB) (L4 c x.1) ((fun hp => AB fbB 0 1 hp
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
    exact retU ge _ hcenv fbB hb nwB hne _ _ _ (.Vint r) _ _
      (fun le m hT => EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (fun _ => rfl)
      (fun hp h => post_A c hm0 _ (fun _ x => mapsto_anyB x) _ hp h)


def P6 : Sep.Assn := fun e le hp => ∃ x, LocalSt (envU fbB hb nwB) (L4 c (.Vint Integers.Int.zero))
  (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB) e le hp

theorem s5 (hcenv : ge.genv_cenv = prog.prog_comp_env) :
    Triple ge (FunctionEntry2 ge) F1 (P5 c fbB hb nwB) (hdS (sp 5 B1))
      (RR (postA c) (P6 c fbB hb nwB)) := by
  unf
  refine triple_lift ge _ _ (fun x => LocalSt (envU fbB hb nwB) (L4 c (.Vint Integers.Int.zero))
    (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K4 c hb nwB)) _ _ _ (fun e le hp h => h) (fun x => ?_)
  have hk : mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K4 c hb nwB = wd32 c c.w
      ∗ (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ AB hb 0 14 ∗ AB nwB 0 8 ∗ AB c.encB 0 8
        ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ mk0 c) := by acx
  refine if_both ge _ _ _ _ _ _ _ _ _ (fun le m hT => ⟨_, _, by evx, rfl⟩) ?_ ?_
  · refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ n, LocalSt (envU fbB hb nwB)
      ((_t'2, .Vint n) :: L4 c (.Vint Integers.Int.zero))
      (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K4 c hb nwB) e le hp) _ _ _ ?_ ?_
    · refine if_both ge _ _ _ _ _ _ _ _ _ (fun le m hT => ⟨_, _, by evx, rfl⟩) ?_ ?_
      · exact triple_conseq ge _ _ (set2 ge _ _ _ _ _ _t'2 _ (.Vint Integers.Int.one) (by lf)
          (fun le m hp hT _ _ => by evx)) (fun _ _ _ x => x) (fun _ _ _ x => ⟨_, x⟩)
          (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
      · exact triple_conseq ge _ _ (set2 ge _ _ _ _ _ _t'2 _ (.Vint Integers.Int.zero) (by lf)
          (fun le m hp hT _ _ => by evx)) (fun _ _ _ x => x) (fun _ _ _ x => ⟨_, x⟩)
          (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
    · refine triple_lift ge _ _ (fun n => LocalSt (envU fbB hb nwB)
        ((_t'2, .Vint n) :: L4 c (.Vint Integers.Int.zero))
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

theorem s6 (hcenv : ge.genv_cenv = prog.prog_comp_env) (rb : List MemVal) (X : Ext ge c.encB rb)
    (hdata : IsPtr c.dataV) (hm0 : c.m0.length = 4) (hne : fbB ≠ hb ∧ fbB ≠ nwB ∧ hb ≠ nwB) :
    Triple ge (FunctionEntry2 ge) F1 (P6 c fbB hb nwB) (hdS (sp 6 B1))
      (RR (postA c) (P6 c fbB hb nwB)) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.fail
  obtain ⟨bL, hsL⟩ := X.lit3
  unf
  refine triple_lift ge _ _ (fun x => LocalSt (envU fbB hb nwB) (L4 c (.Vint Integers.Int.zero))
    (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB)) _ _ _ (fun e le hp h => h) (fun x => ?_)
  refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ b : Bool, LocalSt (envU fbB hb nwB)
      ((_t'3, Val.ofBool b) :: L4 c (.Vint Integers.Int.zero))
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
      ((_t'3, Val.ofBool b) :: L4 c (.Vint Integers.Int.zero))
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
        exact retU ge _ hcenv fbB hb nwB hne _ _ _ (.Vint (Integers.Int.repr 100)) _ _
          (fun le m hT => EvalExpr.Econst_int _ _) (fun _ => rfl)
          (fun hp h => post_A c hm0 _ (fun _ y => y) _ hp h)

theorem s7 (hcenv : ge.genv_cenv = prog.prog_comp_env) (rb : List MemVal) (X : Ext ge c.encB rb)
    (hdata : IsPtr c.dataV) (hm0 : c.m0.length = 4) (hne : fbB ≠ hb ∧ fbB ≠ nwB ∧ hb ≠ nwB) :
    Triple ge (FunctionEntry2 ge) F1 (P6 c fbB hb nwB) (hdS (sp 7 B1))
      (RR (postA c) (P6 c fbB hb nwB)) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.fail
  obtain ⟨bL, hsL⟩ := X.lit4
  unf
  refine triple_lift ge _ _ (fun x => LocalSt (envU fbB hb nwB) (L4 c (.Vint Integers.Int.zero))
    (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB)) _ _ _ (fun e le hp h => h) (fun x => ?_)
  refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ b : Bool, LocalSt (envU fbB hb nwB)
      ((_t'4, Val.ofBool b) :: L4 c (.Vint Integers.Int.zero))
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
      ((_t'4, Val.ofBool b) :: L4 c (.Vint Integers.Int.zero))
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
        exact retU ge _ hcenv fbB hb nwB hne _ _ _ (.Vint (Integers.Int.repr 100)) _ _
          (fun le m hT => EvalExpr.Econst_int _ _) (fun _ => rfl)
          (fun hp h => post_A c hm0 _ (fun _ y => y) _ hp h)

theorem s8 (hcenv : ge.genv_cenv = prog.prog_comp_env) (rb : List MemVal) (X : Ext ge c.encB rb)
    (hdata : IsPtr c.dataV) (hm0 : c.m0.length = 4) (hne : fbB ≠ hb ∧ fbB ≠ nwB ∧ hb ≠ nwB) :
    Triple ge (FunctionEntry2 ge) F1 (P6 c fbB hb nwB) (hdS (sp 8 B1))
      (RR (postA c) (P6 c fbB hb nwB)) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.fail
  obtain ⟨bL, hsL⟩ := X.lit5
  unf
  refine triple_lift ge _ _ (fun x => LocalSt (envU fbB hb nwB) (L4 c (.Vint Integers.Int.zero))
    (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB)) _ _ _ (fun e le hp h => h) (fun x => ?_)
  refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ b : Bool, LocalSt (envU fbB hb nwB)
      ((_t'5, Val.ofBool b) :: L4 c (.Vint Integers.Int.zero))
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
      ((_t'5, Val.ofBool b) :: L4 c (.Vint Integers.Int.zero))
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
        exact retU ge _ hcenv fbB hb nwB hne _ _ _ (.Vint (Integers.Int.repr 100)) _ _
          (fun le m hT => EvalExpr.Econst_int _ _) (fun _ => rfl)
          (fun hp h => post_A c hm0 _ (fun _ y => y) _ hp h)


def P10 : Sep.Assn := LocalSt (envU fbB hb nwB) (L4 c (.Vint Integers.Int.zero))
  (LU fbB hb nwB ∗ K10 c)

theorem s9 (hcenv : ge.genv_cenv = prog.prog_comp_env) :
    Triple ge (FunctionEntry2 ge) F1 (P6 c fbB hb nwB) (hdS (sp 9 B1))
      (RR (postA c) (P10 c fbB hb nwB)) := by
  unf
  refine triple_lift ge _ _ (fun x => LocalSt (envU fbB hb nwB) (L4 c (.Vint Integers.Int.zero))
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
    :: (_t'11, Val.Vint (Integers.Int.zero_ext 8 x)) :: L4 c (.Vint Integers.Int.zero)
  refine triple_seq_fwd ge _ _ _ (LocalSt (envU fbB hb nwB) L9
    (AB c.encB 24 4 ∗ (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ AB hb 0 14 ∗ AB nwB 0 8
        ∗ AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4 ∗ mk0 c))) _ _ _ ?_ ?_
  · refine triple_seq_fwd ge _ _ _ (LocalSt (envU fbB hb nwB) L9
      (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB)) _ _ _ ?_ ?_
    · refine triple_seq_fwd ge _ _ _ (LocalSt (envU fbB hb nwB)
        ((_t'11, Val.Vint (Integers.Int.zero_ext 8 x)) :: L4 c (.Vint Integers.Int.zero))
        (mapsto .Mint8unsigned .Freeable fbB 0 (.Vint x) ∗ K6 c hb nwB)) _ _ _ ?_ ?_
      · refine set2 ge _ _ _ _ _ _t'11 _ _ (by lf) (fun le m hp hT hH hag => ?_)
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

def P11 : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ LocalSt (envU fbB hb nwB) (L13 c n) (LU fbB hb nwB ∗ K10 c) e le hp

theorem s10 :
    Triple ge (FunctionEntry2 ge) F1 (P10 c fbB hb nwB) (hdS (sp 10 B1))
      (RR (postA c) (P11 c fbB hb nwB)) := by
  unfold P10
  have hq : LU fbB hb nwB ∗ K10 c = AB hb 0 14 ∗ (AB fbB 0 1 ∗ AB nwB 0 8 ∗ K10 c) := by acx
  rw [hq]
  refine temps_weak ge _ _ _ _ ((_payload_len, .Vlong c.pl) :: L4 c (.Vint Integers.Int.zero)) _ _ _
    (by ls) ?_
  refine triple_conseq ge _ _ (hdr ge _ _ _ _ c.pl _ (postA c) hb (envU_head _ _ _) (by lf))
    (fun _ _ _ x => x) ?_ (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
  intro e le hp ⟨n, hn, he, hT, hH⟩
  exact ⟨n, hn, he, TempsHold_mono (by ls) hT, by rw [hq]; exact hH⟩

/-- `P11` の `n` を取り出す。 -/
theorem lift_n (P : Nat → Sep.Assn) (s : Stmt) (R : Sep.ExitConds)
    (h : ∀ n, (n = 2 ∨ n = 4 ∨ n = 10) → Triple ge (FunctionEntry2 ge) F1 (P n) s R) :
    Triple ge (FunctionEntry2 ge) F1 (fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10) ∧ P n e le hp) s R := by
  intro k e le hp hf m hd hag ⟨n, hn, hP⟩
  exact h n hn k e le hp hf m hd hag hP

theorem s11 (hcenv : ge.genv_cenv = prog.prog_comp_env) :
    Triple ge (FunctionEntry2 ge) F1 (P11 c fbB hb nwB) (hdS (sp 11 B1))
      (RR (postA c) (P11 c fbB hb nwB)) := by
  unf
  refine lift_n ge _ _ _ (fun n hn => ?_)
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

theorem s12 (rb : List MemVal) (X : Ext ge c.encB rb) (hdata : IsPtr c.dataV) :
    Triple ge (FunctionEntry2 ge) F1 (P11 c fbB hb nwB) (hdS (sp 12 B1))
      (RR (postA c) (P11 c fbB hb nwB)) := by
  obtain ⟨bI, fdI, hsI, hfI, htI, hI⟩ := X.info
  obtain ⟨bL, hsL⟩ := X.lit6
  unf
  refine lift_n ge _ _ _ (fun n hn => ?_)
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


def P13 (rb : List MemVal) : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ ∃ v, LocalSt (envU fbB hb nwB) ((_result, v) :: (_t'8, v) :: L13 c n)
    ((randSpec c.encB rb).post v ∗ K13 c fbB hb nwB) e le hp

theorem s13 (hcenv : ge.genv_cenv = prog.prog_comp_env) (rb : List MemVal) (X : Ext ge c.encB rb)
    (hdata : IsPtr c.dataV) (hm0 : c.m0.length = 4) :
    Triple ge (FunctionEntry2 ge) F1 (P11 c fbB hb nwB) (hdS (sp 13 B1))
      (RR (postA c) (P13 c fbB hb nwB rb)) := by
  obtain ⟨bR, fdR, hsR, hfR, htR, hR⟩ := X.rand
  unf
  refine lift_n ge _ _ _ (fun n hn => ?_)
  refine post_to ge _ _ _ (Q := fun e le hp => ∃ v, LocalSt (envU fbB hb nwB) ((_result, v) :: (_t'8, v) :: L13 c n)
    ((randSpec c.encB rb).post v ∗ K13 c fbB hb nwB) e le hp) ?_ (fun e le hp h => ⟨n, hn, h⟩)
  refine heap_imp ge _ _ _ _ _ (AB c.encB 20 4 ∗ K13 c fbB hb nwB) _ _
    (fun hp h => conv1 (P := mk0 c) (P' := AB c.encB 20 4) (R := K13 c fbB hb nwB) (fun _ y => mk_any hm0 y) (by acx)
      (by have e : LU fbB hb nwB ∗ K10 c = mk0 c ∗ K13 c fbB hb nwB := by acx
          rw [e] at h; exact h)) ?_
  refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ v, LocalSt (envU fbB hb nwB) ((_t'8, v) :: L13 c n)
    ((randSpec c.encB rb).post v ∗ K13 c fbB hb nwB) e le hp) _ _ _ ?_ ?_
  · refine call2 ge _ _ (randSpec c.encB rb) _t'8 _ _ _ _ (AB c.encB 20 4) (K13 c fbB hb nwB)
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
  · refine ex_map ge _ _ _ _ _ (fun v => ?_)
    exact set2 ge _ _ _ _ _ _result _ v (by lf)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm)))

def P14 (rb : List MemVal) : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ LocalSt (envU fbB hb nwB) (L13 c n) (bytesPtsTo c.encB .Freeable 20 rb ∗ K13 c fbB hb nwB) e le hp

theorem s14 (hcenv : ge.genv_cenv = prog.prog_comp_env) (rb : List MemVal)
    (hne : fbB ≠ hb ∧ fbB ≠ nwB ∧ hb ≠ nwB) :
    Triple ge (FunctionEntry2 ge) F1 (P13 c fbB hb nwB rb) (hdS (sp 14 B1))
      (RR (postA c) (P14 c fbB hb nwB rb)) := by
  unf
  refine lift_n ge _ _ _ (fun n hn => ?_)
  refine triple_lift ge _ _ (fun x : Val × Integers.Int => fun e le hp => x.1 = .Vint x.2
      ∧ ((x.2 = Integers.Int.zero ∧ LocalSt (envU fbB hb nwB) ((_result, x.1) :: (_t'8, x.1) :: L13 c n)
            (bytesPtsTo c.encB .Freeable 20 rb ∗ K13 c fbB hb nwB) e le hp)
        ∨ (x.2 ≠ Integers.Int.zero ∧ LocalSt (envU fbB hb nwB) ((_result, x.1) :: (_t'8, x.1) :: L13 c n)
            (AB c.encB 20 4 ∗ K13 c fbB hb nwB) e le hp))) _ _ _ ?_ (fun ⟨v, r⟩ => ?_)
  · intro e le hp ⟨v, he, hT, h1, h2, hd, heq, ⟨r, hv, hor⟩, hk⟩
    refine ⟨(v, r), hv, ?_⟩
    rcases hor with ⟨h0, hb'⟩ | ⟨h0, ha⟩
    · exact Or.inl ⟨h0, he, hT, h1, h2, hd, heq, hb', hk⟩
    · exact Or.inr ⟨h0, he, hT, h1, h2, hd, heq, ha, hk⟩
  refine pure_l ge _ _ _ _ _ _ (fun hv => ?_)
  dsimp only at hv
  subst hv
  refine or_l ge _ _ _ _ _ _ ?_ ?_
  · refine pure_l ge _ _ _ _ _ _ (fun hr => ?_)
    dsimp only at hr
    subst hr
    refine if_val ge _ _ _ _ _ _ false _ _ _ (.Vint Integers.Int.zero)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (fun m => rfl) ?_
    exact skip_to ge _ _ _ _ _ (fun e le hp ⟨he, hT, hH⟩ => ⟨n, hn, he, TempsHold_mono (by ls) hT, hH⟩)
  · refine pure_l ge _ _ _ _ _ _ (fun hr => ?_)
    refine if_val ge _ _ _ _ _ _ true _ _ _ (.Vint r)
      (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by lm)))
      (fun m => by show some (!Integers.Int.eq r Integers.Int.zero) = _; rw [int_eq_false hr]; rfl) ?_
    refine heap_eq ge _ _ _ _ _ (encPost c.encB (AB c.encB 20 4) ∗ LU fbB hb nwB) _ _ (by acx) ?_
    exact retU ge _ hcenv fbB hb nwB hne _ _ _ (.Vint r) _ _
      (fun le m hT => EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (fun _ => rfl) (fun hp h => h)


def P15 (rb : List MemVal) : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ ∃ v, LocalSt (envU fbB hb nwB) (L13 c n)
    ((cpySpec hb n c.encB rb).post v ∗ K15 c fbB hb nwB n) e le hp

theorem s15 (hcenv : ge.genv_cenv = prog.prog_comp_env) (rb : List MemVal) (X : Ext ge c.encB rb) :
    Triple ge (FunctionEntry2 ge) F1 (P14 c fbB hb nwB rb) (hdS (sp 15 B1))
      (RR (postA c) (P15 c fbB hb nwB rb)) := by
  obtain ⟨bC, fdC, hsC, hfC, htC, hC⟩ := X.cpy
  unf
  refine lift_n ge _ _ _ (fun n hn => ?_)
  refine post_to ge _ _ _ (Q := fun e le hp => ∃ v, LocalSt (envU fbB hb nwB) (L13 c n)
    ((cpySpec hb n c.encB rb).post v ∗ K15 c fbB hb nwB n) e le hp) ?_ (fun e le hp h => ⟨n, hn, h⟩)
  have hq : bytesPtsTo c.encB .Freeable 20 rb ∗ K13 c fbB hb nwB
      = (AB hb n 4 ∗ bytesPtsTo c.encB .Freeable 20 rb) ∗ K15 c fbB hb nwB n := by
    simp only [K13, LU]; rw [head_split hb n (hn_le hn)]; acx
  rw [hq]
  refine call_none_ex ge _ _ (cpySpec hb n c.encB rb) _ _ _ _ _ _ bC fdC (hC hb n rb) hfC htC rfl
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

def P16 (rb : List MemVal) : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ LocalSt (envU fbB hb nwB) (L16 c n)
    ((bytesPtsTo hb .Freeable n rb ∗ bytesPtsTo c.encB .Freeable 20 rb) ∗ K15 c fbB hb nwB n) e le hp

theorem s16 (rb : List MemVal) :
    Triple ge (FunctionEntry2 ge) F1 (P15 c fbB hb nwB rb) (hdS (sp 16 B1))
      (RR (postA c) (P16 c fbB hb nwB rb)) := by
  unf
  refine lift_n ge _ _ _ (fun n hn => ?_)
  refine triple_lift ge _ _ (fun v => LocalSt (envU fbB hb nwB) (L13 c n)
    ((cpySpec hb n c.encB rb).post v ∗ K15 c fbB hb nwB n)) _ _ _ (fun e le hp h => h) (fun v => ?_)
  refine post_to ge _ _ _ (triple_set_local ge _ _ _ (L13 c n) (Lk c) _ _hlen _
    (.Vlong (Integers.Int64.repr ((n : Z) + 4))) (by ls) (by lf) (fun le m hp hT _ _ => ?_)) ?_
  · refine EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..)))
      (EvalExpr.Econst_int _ _) ?_
    rcases hn with rfl | rfl | rfl <;> rfl
  · exact fun e le hp h => ⟨n, hn, h⟩

theorem s17 (hcenv : ge.genv_cenv = prog.prog_comp_env) (rb : List MemVal) :
    Triple ge (FunctionEntry2 ge) F1 (P16 c fbB hb nwB rb) (hdS (sp 17 B1))
      (RR (postA c) (P16 c fbB hb nwB rb)) := by
  unf
  refine lift_n ge _ _ _ (fun n hn => ?_)
  refine post_to ge _ _ _ ?_ (fun e le hp h => ⟨n, hn, h⟩)
  have hq : (bytesPtsTo hb .Freeable n rb ∗ bytesPtsTo c.encB .Freeable 20 rb) ∗ K15 c fbB hb nwB n
      = AB c.encB 16 4 ∗ (bytesPtsTo hb .Freeable n rb ∗ bytesPtsTo c.encB .Freeable 20 rb ∗ AB hb 0 n
        ∗ AB hb ((n : Z) + 4) (10 - n) ∗ AB fbB 0 1 ∗ AB nwB 0 8 ∗ AB c.encB 0 8 ∗ AB c.encB 8 8
        ∗ AB c.encB 24 4) := by acx
  rw [hq]
  exact store_any ge _ _ _ _ _ _ _ .Mint32 c.encB _ 16 rfl rfl rfl
    (fun le m hT => lv_enc hcenv (hT.get (by lm)) off_xori)
    (fun le m hT => ⟨_, _, EvalExpr.Econst_int _ _, rfl⟩)

def P18 (rb : List MemVal) : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ ∃ v, LocalSt (envU fbB hb nwB) ((_result, v) :: (_t'9, v) :: L16 c n)
    ((bufqSpec hb n rb nwB).post v ∗ K18 c fbB rb) e le hp

theorem s18 (rb : List MemVal) (X : Ext ge c.encB rb) (hout : IsPtr c.outV) :
    Triple ge (FunctionEntry2 ge) F1 (P16 c fbB hb nwB rb) (hdS (sp 18 B1))
      (RR (postA c) (P18 c fbB hb nwB rb)) := by
  obtain ⟨bQ, fdQ, hsQ, hfQ, htQ, hQ⟩ := X.bufq
  unf
  refine lift_n ge _ _ _ (fun n hn => ?_)
  refine post_to ge _ _ _ (Q := fun e le hp => ∃ v, LocalSt (envU fbB hb nwB) ((_result, v) :: (_t'9, v) :: L16 c n)
    ((bufqSpec hb n rb nwB).post v ∗ K18 c fbB rb) e le hp) ?_ (fun e le hp h => ⟨n, hn, h⟩)
  have hq : (bytesPtsTo hb .Freeable n rb ∗ bytesPtsTo c.encB .Freeable 20 rb) ∗ K15 c fbB hb nwB n
      = (AB hb 0 n ∗ bytesPtsTo hb .Freeable n rb ∗ AB hb ((n : Z) + 4) (10 - n) ∗ AB nwB 0 8)
        ∗ K18 c fbB rb := by acx
  rw [hq]
  refine triple_seq_fwd ge _ _ _ (fun e le hp => ∃ v, LocalSt (envU fbB hb nwB) ((_t'9, v) :: L16 c n)
    ((bufqSpec hb n rb nwB).post v ∗ K18 c fbB rb) e le hp) _ _ _ ?_ ?_
  · refine call2 ge _ _ (bufqSpec hb n rb nwB) _t'9 _ _ _ _ _ (K18 c fbB rb)
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

/-- 出口: `nwritten` を手放し、`mask` の中身を忘れる。 -/
theorem fin_heap (rb : List MemVal) (hrb : rb.length = 4) (k : Integers.Int64) (hp : Heap)
    (h : (mapsto .Mint64 .Freeable nwB 0 (.Vlong k) ∗ (AB hb 0 14 ∗ K18 c fbB rb)) hp) :
    (encPost c.encB (AB c.encB 20 4) ∗ LU fbB hb nwB) hp := by
  have h1 := sep_imp_l (P' := AB nwB 0 8) (fun _ y => mapsto_anyB (chunk := .Mint64) y) h
  have e1 : AB nwB 0 8 ∗ (AB hb 0 14 ∗ K18 c fbB rb) = bytesPtsTo c.encB .Freeable 20 rb
      ∗ (AB nwB 0 8 ∗ AB hb 0 14 ∗ AB fbB 0 1 ∗ AB c.encB 0 8 ∗ AB c.encB 8 8 ∗ AB c.encB 16 4
        ∗ AB c.encB 24 4) := by acx
  rw [e1] at h1
  exact conv1 (P' := AB c.encB 20 4) (fun _ y => mk_any hrb y) (by acx) h1

def P19 (rb : List MemVal) : Sep.Assn := fun e le hp => ∃ n : Nat, (n = 2 ∨ n = 4 ∨ n = 10)
  ∧ ∃ k, LocalSt (envU fbB hb nwB) (L16 c n)
    (mapsto .Mint64 .Freeable nwB 0 (.Vlong k) ∗ (AB hb 0 14 ∗ K18 c fbB rb)) e le hp

theorem s19 (hcenv : ge.genv_cenv = prog.prog_comp_env) (rb : List MemVal) (hrb : rb.length = 4)
    (hne : fbB ≠ hb ∧ fbB ≠ nwB ∧ hb ≠ nwB) :
    Triple ge (FunctionEntry2 ge) F1 (P18 c fbB hb nwB rb) (hdS (sp 19 B1))
      (RR (postA c) (P19 c fbB hb nwB rb)) := by
  unf
  refine lift_n ge _ _ _ (fun n hn => ?_)
  refine triple_lift ge _ _ (fun x : Val × Integers.Int × Integers.Int64 => fun e le hp => x.1 = .Vint x.2.1
      ∧ LocalSt (envU fbB hb nwB) ((_result, x.1) :: (_t'9, x.1) :: L16 c n)
        (mapsto .Mint64 .Freeable nwB 0 (.Vlong x.2.2) ∗ (AB hb 0 14 ∗ K18 c fbB rb)) e le hp) _ _ _ ?_
      (fun ⟨v, r, k⟩ => ?_)
  · intro e le hp ⟨v, he, hT, h1, h2, hd, heq, ⟨r, k, hv, hh⟩, hk⟩
    refine ⟨(v, r, k), hv, he, hT, ?_⟩
    have e1 : (AB hb 0 14 ∗ mapsto .Mint64 .Freeable nwB 0 (.Vlong k)) ∗ K18 c fbB rb
        = mapsto .Mint64 .Freeable nwB 0 (.Vlong k) ∗ (AB hb 0 14 ∗ K18 c fbB rb) := by acx
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
    refine heap_imp ge _ _ _ _ _ _ _ _ (fun hp h => fin_heap c fbB hb nwB rb hrb k hp h) ?_
    exact retU ge _ hcenv fbB hb nwB hne _ _ _ (.Vint r) _ _
      (fun le m hT => EvalExpr.Etempvar _ _ _ (hT.get (by lm))) (fun _ => rfl) (fun hp h => h)

theorem s20 (hcenv : ge.genv_cenv = prog.prog_comp_env) (rb : List MemVal) (hrb : rb.length = 4)
    (hne : fbB ≠ hb ∧ fbB ≠ nwB ∧ hb ≠ nwB) :
    Triple ge (FunctionEntry2 ge) F1 (P19 c fbB hb nwB rb) (hdS (sp 20 B1))
      (RR (postA c) (P19 c fbB hb nwB rb)) := by
  unf
  refine lift_n ge _ _ _ (fun n hn => ?_)
  refine triple_lift ge _ _ (fun k => LocalSt (envU fbB hb nwB) (L16 c n)
    (mapsto .Mint64 .Freeable nwB 0 (.Vlong k) ∗ (AB hb 0 14 ∗ K18 c fbB rb))) _ _ _
    (fun e le hp h => h) (fun k => ?_)
  refine triple_seq_fwd ge _ _ _ (LocalSt (envU fbB hb nwB) ((_t'10, .Vlong k) :: L16 c n)
    (mapsto .Mint64 .Freeable nwB 0 (.Vlong k) ∗ (AB hb 0 14 ∗ K18 c fbB rb))) _ _ _ ?_ ?_
  · refine set2 ge _ _ _ _ _ _t'10 _ _ (by lf) (fun le m hp hT hH hag => ?_)
    refine EvalExpr.Elvalue _ _ _ .Full _ (eval_var_local (envU_nw _ _ _)) (DerefLoc.value .Mint64 _ rfl ?_)
    show Mem.load .Mint64 m nwB 0 = _
    exact cell_ld rfl hH hag
  · refine if_both ge _ _ _ _ _ _ _ _ _ (fun le m hT =>
      ⟨Val.ofBool (!Integers.Int64.eq k (Integers.Int64.repr ((n : Z) + 4))), _,
        EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..)))
          (EvalExpr.Etempvar _ _ _ (hT.get (by lm))) rfl, boolVal_ofBool_tint _ _⟩) ?_ ?_
    · refine triple_seq_fwd ge _ _ _ _ _ _ _ (once_loop ge _ _ _ _ _ (triple_skip ge _ _ _)) ?_
      refine heap_imp ge _ _ _ _ _ _ _ _ (fun hp h => fin_heap c fbB hb nwB rb hrb k hp h) ?_
      exact retU ge _ hcenv fbB hb nwB hne _ _ _ (.Vint (Integers.Int.repr 55)) _ _
        (fun le m hT => EvalExpr.Econst_int _ _) (fun _ => rfl) (fun hp h => h)
    · exact skip_to ge _ _ _ _ _ (fun e le hp ⟨he, hT, hH⟩ => ⟨n, hn, k, he, TempsHold_mono (by ls) hT, hH⟩)

theorem s21 (hcenv : ge.genv_cenv = prog.prog_comp_env) (rb : List MemVal) (hrb : rb.length = 4)
    (hne : fbB ≠ hb ∧ fbB ≠ nwB ∧ hb ≠ nwB) :
    Triple ge (FunctionEntry2 ge) F1 (P19 c fbB hb nwB rb) (sp 21 B1)
      (RR (postA c) Sep.Assn.no) := by
  unf
  refine lift_n ge _ _ _ (fun n hn => ?_)
  refine triple_lift ge _ _ (fun k => LocalSt (envU fbB hb nwB) (L16 c n)
    (mapsto .Mint64 .Freeable nwB 0 (.Vlong k) ∗ (AB hb 0 14 ∗ K18 c fbB rb))) _ _ _
    (fun e le hp h => h) (fun k => ?_)
  refine heap_imp ge _ _ _ _ _ _ _ _ (fun hp h => fin_heap c fbB hb nwB rb hrb k hp h) ?_
  exact retU ge _ hcenv fbB hb nwB hne _ _ _ (.Vint Integers.Int.zero) _ _
    (fun le m hT => EvalExpr.Econst_int _ _) (fun _ => rfl) (fun hp h => h)

end


/-! ## 本体と、関数の仕様 -/

theorem body_after (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx) (rb : List MemVal)
    (X : Ext ge c.encB rb)
    (hpl : Integers.Int64.lt c.pl (Integers.Int64.repr 0) = false)
    (hrem : Integers.Int64.lt (Integers.Int64.repr 0) c.rem = false)
    (hdata : IsPtr c.dataV) (hout : IsPtr c.outV) (hm0 : c.m0.length = 4) (hrb : rb.length = 4)
    (fbB hb nwB : Block) (hne : fbB ≠ hb ∧ fbB ≠ nwB ∧ hb ≠ nwB) :
    Triple ge (FunctionEntry2 ge) F1 (P0 c fbB hb nwB) F1.fn_body
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := postA c } := by
  show Triple _ _ _ _ (sp 0 B1) (RR (postA c) Sep.Assn.no)
  refine chain ge _ _ B1 0 _ _ _ _ rfl (s0 ge c fbB hb nwB) ?_
  refine chain ge _ _ B1 1 _ _ _ _ rfl (s1 ge c fbB hb nwB hpl) ?_
  refine chain ge _ _ B1 2 _ _ _ _ rfl (s2 ge c fbB hb nwB hcenv hrem) ?_
  refine chain ge _ _ B1 3 _ _ _ _ rfl (s3 ge c fbB hb nwB hcenv rb X hdata) ?_
  refine chain ge _ _ B1 4 _ _ _ _ rfl (s4 ge c fbB hb nwB hcenv hm0 hne) ?_
  refine chain ge _ _ B1 5 _ _ _ _ rfl (s5 ge c fbB hb nwB hcenv) ?_
  refine chain ge _ _ B1 6 _ _ _ _ rfl (s6 ge c fbB hb nwB hcenv rb X hdata hm0 hne) ?_
  refine chain ge _ _ B1 7 _ _ _ _ rfl (s7 ge c fbB hb nwB hcenv rb X hdata hm0 hne) ?_
  refine chain ge _ _ B1 8 _ _ _ _ rfl (s8 ge c fbB hb nwB hcenv rb X hdata hm0 hne) ?_
  refine chain ge _ _ B1 9 _ _ _ _ rfl (s9 ge c fbB hb nwB hcenv) ?_
  refine chain ge _ _ B1 10 _ _ _ _ rfl (s10 ge c fbB hb nwB) ?_
  refine chain ge _ _ B1 11 _ _ _ _ rfl (s11 ge c fbB hb nwB hcenv) ?_
  refine chain ge _ _ B1 12 _ _ _ _ rfl (s12 ge c fbB hb nwB rb X hdata) ?_
  refine chain ge _ _ B1 13 _ _ _ _ rfl (s13 ge c fbB hb nwB hcenv rb X hdata hm0) ?_
  refine chain ge _ _ B1 14 _ _ _ _ rfl (s14 ge c fbB hb nwB hcenv rb hne) ?_
  refine chain ge _ _ B1 15 _ _ _ _ rfl (s15 ge c fbB hb nwB hcenv rb X) ?_
  refine chain ge _ _ B1 16 _ _ _ _ rfl (s16 ge c fbB hb nwB rb) ?_
  refine chain ge _ _ B1 17 _ _ _ _ rfl (s17 ge c fbB hb nwB hcenv rb) ?_
  refine chain ge _ _ B1 18 _ _ _ _ rfl (s18 ge c fbB hb nwB rb X hout) ?_
  refine chain ge _ _ B1 19 _ _ _ _ rfl (s19 ge c fbB hb nwB hcenv rb hrb hne) ?_
  refine chain ge _ _ B1 20 _ _ _ _ rfl (s20 ge c fbB hb nwB hcenv rb hrb hne) ?_
  exact s21 ge c fbB hb nwB hcenv rb hrb hne

/-- 関数の仕様（U1）。前提: 引数がこの値で、`*enc` を所有している。事後条件: `*enc` の所有を返す。 -/
def specA (c : Ctx) : FunSpec where
  tyargs := [tptr easyT, tptr encT, tuint, tlong, tptr (Ty.Tstruct _bufq noattr)]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [c.dataV, .Vptr c.encB Integers.Ptrofs.zero, .Vint c.fl, .Vlong c.pl, c.outV]
    ∧ encPre c hp
  post := postA c
  measure := fun _ => 0

theorem add_frame_entry_wf :
    listNorepet (varNames F1.fn_vars) ∧ listNorepet (varNames F1.fn_params)
    ∧ listDisjoint (varNames F1.fn_params) (varNames F1.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **修正後の `ws_enc_add_frame`（U1）**: `Curl_rand` が `enc->mask` に `rb` を書くとき、`Curl_bufq_write` に渡すヘッダの最後の
    4バイトは `rb`（`bufqSpec` の前提）。`payload_len` が負でなく、`enc->payload_remain` が正でない入力について。 -/
theorem add_frame_after (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx) (rb : List MemVal)
    (X : Ext ge c.encB rb)
    (hpl : Integers.Int64.lt c.pl (Integers.Int64.repr 0) = false)
    (hrem : Integers.Int64.lt (Integers.Int64.repr 0) c.rem = false)
    (hdata : IsPtr c.dataV) (hout : IsPtr c.outV) (hm0 : c.m0.length = 4) (hrb : rb.length = 4)
    (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal F1) (specA c) vs := by
  by_cases hvs : vs = [c.dataV, .Vptr c.encB Integers.Ptrofs.zero, .Vint c.fl, .Vlong c.pl, c.outV]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := add_frame_entry_wf
  refine satisfies_internal ge (FunctionEntry2 ge) F1 _ _
    (fun e le hp => ∃ x : Block × Block × Block, (x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧ x.2.1 ≠ x.2.2)
      ∧ P0 c x.1 x.2.1 x.2.2 e le hp)
    (fun m hp hf hpre hd hag => ?_)
    (triple_lift ge _ _ _ _ _ _ (fun e le hp h => h) (fun x => pure_l ge _ _ _ _ _ _ (fun hne =>
      body_after ge hcenv c rb X hpl hrem hdata hout hm0 hrb x.1 x.2.1 x.2.2 hne)))
  let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv tuchar)
  let a2 := Mem.alloc a1.1 0 (sizeof ge.genv_cenv (tarray tuchar 14))
  let a3 := Mem.alloc a2.1 0 (sizeof ge.genv_cenv tulong)
  have hav : AllocVariables ge.genv_cenv emptyEnv m F1.fn_vars (envU a1.2 a2.2 a3.2) a3.1 :=
    .cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _)))
  obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav hnv
    (by
      intro v hv
      simp only [F1, f_ws_enc_add_frame, List.mem_cons, List.mem_nil_iff, or_false] at hv
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
        (createUndefTemps F1.fn_temps))))),
    a3.1, hl, FunctionEntry2.intro hnv hnp hdisj hav rfl,
    Heap.disjoint_union_left.mpr ⟨hd, Heap.disjoint_comm dfh⟩, ?_, ?_⟩
  · rw [Heap.union_assoc, Heap.union_comm (Heap.disjoint_comm dfh), ← Heap.union_assoc]
    exact hagl
  · refine ⟨(a1.2, a2.2, a3.2), hne, rfl, ?_, ⟨hp, hl, dph, rfl, hpre.2, hL⟩⟩
    intro q hq
    simp only [Lk, List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> rfl

end Deb2025_10148C
