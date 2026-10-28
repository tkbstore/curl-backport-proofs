/-
CVE-2026-3805（research/backport-proof-debian/cases/CVE-2026-3805.md）: 修正前・修正後の証明で共通に使う部分。

- 文字列の所有（`arr`・`strAt`・`ownStr`）と、1文字の読み書き
- 外部関数5つの仕様
- 規則を `LocalSt` の形にしたもの（所有の並べ替えは `ac_rfl` で行う）
- `for(; *p; p++) { if(*p == '/') *p = '\\'; }` の形のループの規則（修正前・修正後で共通）
-/
import GenDeb2026_3805UpAfter
import Case3Common
import Case4debCommon
open CC CC.Sep CC.HProp
open Deb2026_3805_up_after
open Case5C (addr RR return_const)
open Case4debC (IsPtr mapsto_weakValid eval_deref_temp lv_field loadResult_ptr cast_ptr)

set_option maxRecDepth 20000

namespace Deb2026_3805C

instance : Std.Associative (α := HProp) (· ∗ ·) := ⟨sep_assoc_eq⟩
instance : Std.Commutative (α := HProp) (· ∗ ·) := ⟨sep_comm_eq⟩

/-! ## 文字列の所有 -/

/-- 1文字（`char`、符号付き 8 bit）のセル。 -/
def chr (b : Block) (f : Nat → Integers.Int) : Nat → _root_.Int → HProp :=
  fun i off => mapsto .Mint8signed .Freeable b off (.Vint (f i))

/-- ブロック `b` の先頭から `N` 文字。中身は `f`。 -/
def arr (b : Block) (f : Nat → Integers.Int) (N : Nat) : HProp := arrayOf (chr b f) 1 0 N

/-- 1文字の値が `char` に収まる（符号付き 8 bit への拡張で変わらない）。 -/
def Chars (f : Nat → Integers.Int) : Prop := ∀ i, Integers.Int.sign_ext 8 (f i) = f i

/-- 位置 `pos` から `len` の手前までは 0 でなく、`len` が 0（NUL 終端）。 -/
def Tail (f : Nat → Integers.Int) (pos len : Nat) : Prop :=
  pos ≤ len ∧ (∀ j, pos ≤ j → j < len → Integers.Int.eq (f j) Integers.Int.zero = false)
  ∧ f len = Integers.Int.zero ∧ Chars f ∧ len + 2 < 18446744073709551616

/-- ブロック `b` の先頭に、長さ `n` の NUL 終端の文字列。 -/
def strAt (b : Block) (f : Nat → Integers.Int) (n : Nat) : HProp := ⌜Tail f 0 n⌝ ∗ arr b f (n + 1)

def nullV : Val := .Vlong Integers.Int64.zero

/-- NULL か、ブロックの先頭にある文字列（`malloc` した領域として手放せるもの）。 -/
def ownStr (v : Val) : HProp := fun h =>
  (v = nullV ∧ emp h) ∨ ∃ b f n, v = .Vptr b Integers.Ptrofs.zero ∧ strAt b f n h

def upd (f : Nat → Integers.Int) (i : Nat) (v : Integers.Int) : Nat → Integers.Int :=
  fun j => if j = i then v else f j

theorem ofs_i (i : Nat) : (0 : _root_.Int) + 1 * (i : _root_.Int) = (i : _root_.Int) := by omega

theorem arr_split {b : Block} {f : Nat → Integers.Int} {N i : Nat} (hi : i < N) :
    arr b f N = mapsto .Mint8signed .Freeable b (i : _root_.Int) (.Vint (f i))
      ∗ arrayOfRest (chr b f) 1 0 N i := by
  unfold arr
  rw [arrayOf_split (chr b f) 1 0 N i hi, ofs_i]
  rfl

theorem arr_load {b : Block} {f : Nat → Integers.Int} {N i : Nat} {h : Heap} {m : Mem}
    (hA : arr b f N h) (hag : Heap.Agrees h m) (hi : i < N) :
    Mem.load .Mint8signed m b (i : _root_.Int) = some (.Vint (Integers.Int.sign_ext 8 (f i))) := by
  rw [arr_split hi] at hA
  obtain ⟨h1, h2, _, rfl, hm, _⟩ := hA
  exact mapsto_load (by decide) hm (Heap.Agrees_union_left hag)

theorem arr_valid {b : Block} {f : Nat → Integers.Int} {N i : Nat} {h : Heap} {m : Mem}
    (hA : arr b f N h) (hag : Heap.Agrees h m) (hi : i < N) :
    Mem.weakValidPointer m b (i : _root_.Int) = true := by
  rw [arr_split hi] at hA
  obtain ⟨h1, h2, _, rfl, hm, _⟩ := hA
  exact mapsto_weakValid (by decide) hm (Heap.Agrees_union_left hag) (by decide)

/-- 2つの `arr` が分離して所有されていれば、ブロックは違う。 -/
theorem arr_ne {b1 b2 : Block} {f1 f2 : Nat → Integers.Int} {N1 N2 : Nat} {h1 h2 : Heap}
    (a1 : arr b1 f1 N1 h1) (a2 : arr b2 f2 N2 h2) (hd : Heap.disjoint h1 h2)
    (p1 : 0 < N1) (p2 : 0 < N2) : b1 ≠ b2 := by
  intro heq
  subst heq
  rw [arr_split p1] at a1
  rw [arr_split p2] at a2
  obtain ⟨g1, r1, d1, rfl, m1, _⟩ := a1
  obtain ⟨g2, r2, d2, rfl, m2, _⟩ := a2
  obtain ⟨_, hb1⟩ := pure_sep_elim m1
  obtain ⟨_, hb2⟩ := pure_sep_elim m2
  have o1 := bytesPtsTo_ownsRange _ _ _ _ _ hb1 0 (by rw [length_encodeVal]; decide)
  have o2 := bytesPtsTo_ownsRange _ _ _ _ _ hb2 0 (by rw [length_encodeVal]; decide)
  obtain ⟨c1, e1⟩ : ∃ c, g1 b1 (((0 : Nat) : _root_.Int) + ((0 : Nat) : _root_.Int)) = some c :=
    ⟨_, o1⟩
  obtain ⟨c2, e2⟩ : ∃ c, g2 b1 (((0 : Nat) : _root_.Int) + ((0 : Nat) : _root_.Int)) = some c :=
    ⟨_, o2⟩
  have u1 : Heap.union g1 r1 b1 _ = some c1 := Heap.union_of_left e1
  have u2 : Heap.union g2 r2 b1 _ = some c2 := Heap.union_of_left e2
  rw [Case1C.none_of_disjoint hd u1] at u2
  cases u2

theorem mapsto_any {v : Val} {b : Block} {h : Heap}
    (hm : mapsto Mptr .Freeable b 0 v h) : anyBytes .Freeable b 0 8 h := by
  obtain ⟨_, hb⟩ := pure_sep_elim hm
  have := anyBytes_of_bytesPtsTo hb
  rwa [length_encodeVal] at this

/-! ## 外部関数の仕様（弱く書く） -/

/-- `Curl_urldecode(string, 0, &path, NULL, REJECT_CTRL)`: 失敗のコードか、`*ostring`（局所変数 `path` のブロック `bp`）に
    新しい NUL 終端の文字列の先頭を書いて 0 を返す。 -/
def udSpec (bp : Block) : FunSpec where
  tyargs := [tptr tschar, tulong, tptr (tptr tschar), tptr tulong, tint]
  tyres := tint
  cc := cc_default
  pre := fun _ hp => anyBytes .Freeable bp 0 8 hp
  post := fun v hp =>
    (∃ x : Block × (Nat → Integers.Int) × Nat, v = .Vint Integers.Int.zero
      ∧ (mapsto Mptr .Freeable bp 0 (.Vptr x.1 Integers.Ptrofs.zero) ∗ strAt x.1 x.2.1 x.2.2) hp)
    ∨ (∃ r : Integers.Int, (v = .Vint r ∧ r ≠ Integers.Int.zero) ∧ anyBytes .Freeable bp 0 8 hp)
  measure := fun _ => 0

/-- `Curl_cstrdup(s)`: NULL か、新しいブロックの先頭の NUL 終端の文字列（中身は問わない）を返す。 -/
def dupSpec : FunSpec where
  tyargs := [tptr tschar]
  tyres := tptr tschar
  cc := cc_default
  pre := fun _ hp => emp hp
  post := fun v hp => ownStr v hp
  measure := fun _ => 0

/-- `Curl_cfree(p)`: NULL か、文字列の所有を受け取って手放す。 -/
def freeSpec : FunSpec where
  tyargs := [tptr tvoid]
  tyres := tvoid
  cc := cc_default
  pre := fun vargs hp => ∃ v, vargs = [v] ∧ ownStr v hp
  post := fun _ hp => emp hp
  measure := fun _ => 0

/-- `strchr(s, c)`（`s` はブロック `b` の先頭の長さ `n` の文字列）: NULL か、終端より前の位置を返す。文字は問わない。 -/
def chrSpec (b : Block) (f : Nat → Integers.Int) (n : Nat) : FunSpec where
  tyargs := [tptr tschar, tint]
  tyres := tptr tschar
  cc := cc_default
  pre := fun vargs hp => (∃ c, vargs = [.Vptr b Integers.Ptrofs.zero, .Vint c]) ∧ strAt b f n hp
  post := fun v hp =>
    (⌜v = nullV ∨ ∃ k o, k < n ∧ Integers.Ptrofs.unsigned o = (k : _root_.Int) ∧ v = .Vptr b o⌝
      ∗ strAt b f n) hp
  measure := fun _ => 0

/-- `Curl_failf(data, fmt)`（可変長引数）: 何もしない。 -/
def failSpec : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tptr tschar]
  tyres := tvoid
  cc := { cc_vararg := some 2, cc_unproto := false, cc_structret := false }
  pre := fun _ hp => emp hp
  post := fun _ hp => emp hp
  measure := fun _ => 0

/-! ## 規則（`LocalSt` の形） -/

/-- 呼び出し（戻り値を一時変数に入れる）。呼ばれる側は `Hpre` だけを受け取る。 -/
theorem call_some (ge fe f) (S : FunSpec) (id : Ident) (a : Expr) (al : List Expr)
    (E : Env) (l : List (Ident × Val)) (Hpre Hkeep : HProp) (vargs : List Val)
    (fb : Block) (fd : FunDef) (Q : Val → HProp)
    (hspec : ∀ vs, SatisfiesAt ge fe fd S vs) (hfind : FuncPtr ge fb fd)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun (typeof a) = .f S.tyargs S.tyres S.cc)
    (hcallee : ∀ le m, TempsHold l le → EvalExpr ge E le m a (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge E le m al S.tyargs vargs)
    (hpre : ∀ h, Hpre h → S.pre vargs h)
    (hpost : ∀ v h, S.post v h → Q v h) :
    Triple ge fe f (LocalSt E l (Hpre ∗ Hkeep)) (.Scall (some id) a al)
      (.only (fun e le hp => ∃ v, LocalSt E (setLocal l id v) (Q v ∗ Hkeep) e le hp)) := by
  refine triple_call ge fe f S (some id) a al _ _ fb fd hspec hfind hty hclass
    (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, h1, h2, hd, heq, hH1, hH2⟩ := hP
  subst he
  refine ⟨vargs, h1, h2, hd, heq, hcallee le m hT, hargs le m hT, hpre h1 hH1,
    fun v h1' hS hd' => ⟨v, rfl, ?_, h1', h2, hd', rfl, hpost v h1' hS, hH2⟩⟩
  exact TempsHold_set (fun _ hq => (mem_dropId hq).2)
    (TempsHold_mono (fun _ hq => (mem_dropId hq).1) hT)

/-- 呼び出し（戻り値を捨てる）。 -/
theorem call_none (ge fe f) (S : FunSpec) (a : Expr) (al : List Expr)
    (E : Env) (l : List (Ident × Val)) (Hpre Hkeep : HProp) (vargs : List Val)
    (fb : Block) (fd : FunDef)
    (hspec : ∀ vs, SatisfiesAt ge fe fd S vs) (hfind : FuncPtr ge fb fd)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun (typeof a) = .f S.tyargs S.tyres S.cc)
    (hcallee : ∀ le m, TempsHold l le → EvalExpr ge E le m a (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge E le m al S.tyargs vargs)
    (hpre : ∀ h, Hpre h → S.pre vargs h)
    (hpost : ∀ v h, S.post v h → emp h) :
    Triple ge fe f (LocalSt E l (Hpre ∗ Hkeep)) (.Scall none a al) (.only (LocalSt E l Hkeep)) := by
  refine triple_call ge fe f S none a al _ _ fb fd hspec hfind hty hclass
    (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, h1, h2, hd, heq, hH1, hH2⟩ := hP
  subst he
  refine ⟨vargs, h1, h2, hd, heq, hcallee le m hT, hargs le m hT, hpre h1 hH1,
    fun v h1' hS hd' => ⟨rfl, hT, ?_⟩⟩
  have := hpost v h1' hS
  rw [emp] at this
  subst this
  rw [Heap.emp_union]
  exact hH2

/-- 所有の並べ替え（等式で与える）。 -/
theorem heap_eq (ge fe f) (E : Env) (l : List (Ident × Val)) (H H' : HProp) (s : Stmt)
    (R : Sep.ExitConds) (heq : H = H') (h : Triple ge fe f (LocalSt E l H') s R) :
    Triple ge fe f (LocalSt E l H) s R := heq ▸ h

/-- セルへの代入。左辺と右辺の評価はメモリを読まない。 -/
theorem assign_cell (ge fe f) (E : Env) (l : List (Ident × Val)) (R : HProp)
    (a1 a2 : Expr) (chunk : Chunk) (b : Block) (ofs : Integers.Ptrofs) (o : Z)
    (vold vnew : Val)
    (hacc : accessMode (typeof a1) = .By_value chunk)
    (ho : Integers.Ptrofs.unsigned ofs = o)
    (hlv : ∀ le m, TempsHold l le → EvalLvalue ge E le m a1 b ofs .Full)
    (hev : ∀ le m, TempsHold l le →
      ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some vnew) :
    Triple ge fe f (LocalSt E l (mapsto chunk .Freeable b o vold ∗ R)) (.Sassign a1 a2)
      (.only (LocalSt E l (mapsto chunk .Freeable b o vnew ∗ R))) := by
  subst ho
  refine triple_assign ge fe f _ _ a1 a2 chunk .Freeable b ofs (by decide) hacc
    (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, h1, h2, hd, heq, hm, hr⟩ := hP
  subst he
  refine ⟨vold, vnew, h1, h2, hd, heq, hm, hlv le m hT, hev le m hT, fun h1' hm' hd' => ?_⟩
  exact ⟨rfl, hT, h1', h2, hd', rfl, hm', hr⟩

/-- 文字への代入（`*p = c;`）。 -/
theorem assign_byte (ge fe f) (E : Env) (l : List (Ident × Val)) (R : HProp)
    (a1 a2 : Expr) (b : Block) (ofs : Integers.Ptrofs) (fc : Nat → Integers.Int) (N i : Nat)
    (vnew : Integers.Int) (hi : i < N)
    (hty : typeof a1 = tschar)
    (ho : Integers.Ptrofs.unsigned ofs = (i : _root_.Int))
    (hlv : ∀ le m, TempsHold l le → EvalLvalue ge E le m a1 b ofs .Full)
    (hev : ∀ le m, TempsHold l le →
      ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) tschar m = some (.Vint vnew)) :
    Triple ge fe f (LocalSt E l (arr b fc N ∗ R)) (.Sassign a1 a2)
      (.only (LocalSt E l (arr b (upd fc i vnew) N ∗ R))) := by
  refine triple_assign ge fe f _ _ a1 a2 .Mint8signed .Freeable b ofs (by decide)
    (by rw [hty]; rfl) (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, hA, hR, hd, heq, hAr, hr⟩ := hP
  subst he
  rw [arr_split hi] at hAr
  obtain ⟨h1, h2, hd12, rfl, hm, hrest⟩ := hAr
  rw [Heap.disjoint_union_left] at hd
  obtain ⟨v2, hev2, hcast⟩ := hev le m hT
  refine ⟨.Vint (fc i), .Vint vnew, h1, Heap.union h2 hR,
    Heap.disjoint_union_right.mpr ⟨hd12, hd.1⟩, by rw [heq, Heap.union_assoc], by rw [ho]; exact hm,
    hlv le m hT, ⟨v2, hev2, by rw [hty]; exact hcast⟩, fun h1' hm' hd' => ?_⟩
  rw [Heap.disjoint_union_right] at hd'
  refine ⟨rfl, hT, Heap.union h1' h2, hR,
    Heap.disjoint_union_left.mpr ⟨hd'.2, hd.2⟩, by rw [Heap.union_assoc], ?_, hr⟩
  unfold arr
  rw [arrayOf_update (chr b fc) (chr b (upd fc i vnew)) 1 0 N i hi
    (fun j _ hne => by funext off; simp [chr, upd, hne]), ofs_i]
  refine ⟨h1', h2, hd'.1, rfl, ?_, hrest⟩
  rw [← ho]
  simpa [chr, upd] using hm'

/-! ## `for(; *p; p++) { if(*p == '/') *p = '\\'; }` のループ -/

def scanBody (p ta tb : Ident) : Stmt :=
  .Ssequence
    (.Ssequence (.Sset ta (.Ederef (.Etempvar p (tptr tschar)) tschar))
      (.Sifthenelse (.Etempvar ta tschar) .Sskip .Sbreak))
    (.Ssequence (.Sset tb (.Ederef (.Etempvar p (tptr tschar)) tschar))
      (.Sifthenelse (.Ebinop .Oeq (.Etempvar tb tschar) (.Econst_int (Integers.Int.repr 47) tint) tint)
        (.Sassign (.Ederef (.Etempvar p (tptr tschar)) tschar) (.Econst_int (Integers.Int.repr 92) tint))
        .Sskip))

def scanIncr (p : Ident) : Stmt :=
  .Sset p (.Ebinop .Oadd (.Etempvar p (tptr tschar)) (.Econst_int (Integers.Int.repr 1) tint) (tptr tschar))

/-- 前提から事実を取り出す。 -/
theorem triple_lift {α : Sort u} (ge fe f) (P : α → Sep.Assn) (s : Stmt) (R : Sep.ExitConds)
    (Q : Sep.Assn) (hQ : ∀ e le hp, Q e le hp → ∃ x, P x e le hp)
    (h : ∀ x, Triple ge fe f (P x) s R) : Triple ge fe f Q s R := by
  intro k e le hp hf m hd hag hq
  obtain ⟨x, hx⟩ := hQ e le hp hq
  exact h x k e le hp hf m hd hag hx

/-- `*p`（`p` は文字の位置 `pos` を指す）。 -/
theorem eval_char {ge : CGenv} {E : Env} {le : TempEnv} {m : Mem} {p : Ident} {b : Block}
    {o : Integers.Ptrofs} {fc : Nat → Integers.Int} {N pos : Nat} {h : Heap}
    (hle : le.get p = some (.Vptr b o)) (ho : Integers.Ptrofs.unsigned o = (pos : _root_.Int))
    (hA : arr b fc N h) (hag : Heap.Agrees h m) (hi : pos < N) (hch : Chars fc) :
    EvalExpr ge E le m (.Ederef (.Etempvar p (tptr tschar)) tschar) (.Vint (fc pos)) := by
  refine EvalExpr.Elvalue _ b o .Full _ (EvalLvalue.Ederef _ _ b o (EvalExpr.Etempvar p _ _ hle))
    (DerefLoc.value .Mint8signed _ rfl ?_)
  show Mem.load _ m b (Integers.Ptrofs.unsigned o) = _
  rw [ho, arr_load hA hag hi, hch pos]

theorem boolVal_char (c : Integers.Int) (m : Mem) :
    Cop.boolVal (.Vint c) tschar m = some (!Integers.Int.eq c Integers.Int.zero) := rfl

theorem cmp47 (ce : CompositeEnv) (c : Integers.Int) (m : Mem) :
    Cop.semBinaryOperation ce .Oeq (.Vint c) tschar (.Vint (Integers.Int.repr 47)) tint m
      = some (Val.ofBool (Integers.Int.eq c (Integers.Int.repr 47))) := rfl

theorem int_eq_self (x : Integers.Int) : Integers.Int.eq x x = true := by
  simp [Integers.Int.eq, Integers.MI.eq]

theorem incr_ofs (ce : CompositeEnv) (o : Integers.Ptrofs) (pos : Nat)
    (ho : Integers.Ptrofs.unsigned o = (pos : _root_.Int)) (hb : pos + 1 < 18446744073709551616) :
    Integers.Ptrofs.unsigned (Integers.Ptrofs.add o
      (Integers.Ptrofs.mul (Integers.Ptrofs.repr (sizeof ce tschar))
        (Cop.ptrofsOfInt .Signed (Integers.Int.repr 1)))) = ((pos + 1 : Nat) : _root_.Int) := by
  have h1 : Integers.Ptrofs.mul (Integers.Ptrofs.repr (sizeof ce tschar))
      (Cop.ptrofsOfInt .Signed (Integers.Int.repr 1)) = Integers.Ptrofs.repr ((1 : Nat) : _root_.Int) := by
    have hs : sizeof ce tschar = 1 := rfl
    rw [hs]; decide
  rw [h1, ptrofs_add_unsigned o 1 ?_, ho]
  · push_cast; rfl
  · have h2 : (o.toNat : _root_.Int) = (pos : _root_.Int) := by rw [← ho]; rfl
    omega

def scanOut (E : Env) (l : List (Ident × Val)) (R : HProp) (p : Ident) (b : Block) (len : Nat) : Sep.Assn :=
  fun e le hp => ∃ fc o, LocalSt E ((p, .Vptr b o) :: l) (arr b fc (len + 1) ∗ R) e le hp

def scanInv (E : Env) (l : List (Ident × Val)) (R : HProp) (p : Ident) (b : Block) (len : Nat)
    (n : Nat) : Sep.Assn :=
  fun e le hp => ∃ fc o, n ≤ len ∧ Integers.Ptrofs.unsigned o = ((len - n : Nat) : _root_.Int)
    ∧ Tail fc (len - n) len ∧ LocalSt E ((p, .Vptr b o) :: l) (arr b fc (len + 1) ∗ R) e le hp

def scanJ (E : Env) (l : List (Ident × Val)) (R : HProp) (p : Ident) (b : Block) (len : Nat)
    (n : Nat) : Sep.Assn :=
  fun e le hp => ∃ fc o, 0 < n ∧ n ≤ len ∧ Integers.Ptrofs.unsigned o = ((len - n : Nat) : _root_.Int)
    ∧ Tail fc (len - n) len ∧ LocalSt E ((p, .Vptr b o) :: l) (arr b fc (len + 1) ∗ R) e le hp

theorem tail_upd92 {fc : Nat → Integers.Int} {pos len : Nat} (ht : Tail fc pos len) (hlt : pos < len) :
    Tail (upd fc pos (Integers.Int.repr 92)) pos len := by
  obtain ⟨hle, hnz, hz, hch, hb⟩ := ht
  refine ⟨hle, fun j h1 h2 => ?_, ?_, fun j => ?_, hb⟩
  · by_cases hj : j = pos
    · simp [upd, hj]; decide
    · simp [upd, hj]; exact hnz j h1 h2
  · simp [upd, show len ≠ pos by omega, hz]
  · by_cases hj : j = pos
    · simp [upd, hj]; decide
    · simp [upd, hj]; exact hch j

theorem tail_next {fc : Nat → Integers.Int} {pos len : Nat} (ht : Tail fc pos len) (hlt : pos < len) :
    Tail fc (pos + 1) len := by
  obtain ⟨_, hnz, hz, hch, hb⟩ := ht
  exact ⟨hlt, fun j h1 h2 => hnz j (by omega) h2, hz, hch, hb⟩

theorem sext92 : Integers.Int.sign_ext 8 (Integers.Int.repr 92) = Integers.Int.repr 92 := by decide

theorem scan_loop (ge fe f) (E : Env) (l : List (Ident × Val)) (R : HProp) (p ta tb : Ident)
    (b : Block) (len : Nat)
    (hnl : ∀ q ∈ l, q.1 ≠ p ∧ q.1 ≠ ta ∧ q.1 ≠ tb) (hpa : p ≠ ta) (hpb : p ≠ tb) (hab : ta ≠ tb) :
    ∀ n, Triple ge fe f (scanInv E l R p b len n) (.Sloop (scanBody p ta tb) (scanIncr p))
      (.only (scanOut E l R p b len)) := by
  refine Sep.triple_loop ge fe f _ _ (scanJ E l R p b len) _ _ (fun n => ?_) (fun n => ?_)
  · -- 本体
    refine triple_lift ge fe f (fun (x : (Nat → Integers.Int) × Integers.Ptrofs) =>
      fun e le hp => n ≤ len ∧ Integers.Ptrofs.unsigned x.2 = ((len - n : Nat) : _root_.Int)
        ∧ Tail x.1 (len - n) len
        ∧ LocalSt E ((p, .Vptr b x.2) :: l) (arr b x.1 (len + 1) ∗ R) e le hp) _ _ _
      (fun e le hp ⟨fc, o, h⟩ => ⟨(fc, o), h⟩) (fun ⟨fc, o⟩ => ?_)
    refine triple_lift ge fe f (fun (_ : n ≤ len ∧ Integers.Ptrofs.unsigned o = ((len - n : Nat) : _root_.Int)
        ∧ Tail fc (len - n) len) =>
      LocalSt E ((p, .Vptr b o) :: l) (arr b fc (len + 1) ∗ R)) _ _ _
      (fun e le hp ⟨h1, h2, h3, h4⟩ => ⟨⟨h1, h2, h3⟩, h4⟩) (fun ⟨hn, ho, ht⟩ => ?_)
    have hch := ht.2.2.2.1
    have hpos : len - n < len + 1 := by omega
    have hn1 : ∀ q ∈ (p, Val.Vptr b o) :: l, q.1 ≠ ta := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hpa
      · exact (hnl q hq).2.1
    have hn2 : ∀ q ∈ (ta, Val.Vint (fc (len - n))) :: (p, Val.Vptr b o) :: l, q.1 ≠ tb := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hab
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hpb
      · exact (hnl q hq).2.2
    have hev : ∀ le m hp, TempsHold ((p, Val.Vptr b o) :: l) le → (arr b fc (len + 1) ∗ R) hp →
        Heap.Agrees hp m → EvalExpr ge E le m (.Ederef (.Etempvar p (tptr tschar)) tschar)
          (.Vint (fc (len - n))) := by
      intro le m hp hT hH hag
      obtain ⟨h1, h2, hd, rfl, hA, _⟩ := hH
      exact eval_char (hT.get (List.mem_cons_self ..)) ho hA (Heap.Agrees_union_left hag) hpos hch
    by_cases hz : n = 0
    · -- 終端: break
      subst hz
      have hfz : fc (len - 0) = Integers.Int.zero := by simpa using ht.2.2.1
      refine triple_seq ge fe f _ Sep.Assn.no _ _ _
        (triple_seq_fwd ge fe f _ _ _ _ _
          (triple_set_local ge fe f E _ _ _ ta _ _ (fun _ h => h) hn1 hev) ?_)
        (triple_vacuous ge fe f _ _)
      refine triple_if_local ge fe f E _ _ _ (!Integers.Int.eq (fc (len - 0)) Integers.Int.zero) _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..)),
          boolVal_char _ m⟩) ?_
      rw [hfz, int_eq_self]
      exact triple_conseq ge fe f (triple_break ge fe f _) (fun _ _ _ x => x)
        (fun _ _ _ x => x.elim)
        (fun e le hp ⟨he, hT, hH⟩ => ⟨fc, o, he, TempsHold_mono (fun q hq => List.mem_cons_of_mem _ hq) hT, hH⟩)
        (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
    have hlt : len - n < len := by omega
    have hne0 := ht.2.1 (len - n) (Nat.le_refl _) hlt
    refine triple_seq ge fe f _
      (LocalSt E ((ta, .Vint (fc (len - n))) :: (p, .Vptr b o) :: l) (arr b fc (len + 1) ∗ R)) _ _ _
      (triple_seq_fwd ge fe f _ _ _ _ _
        (triple_set_local ge fe f E _ _ _ ta _ _ (fun _ h => h) hn1 hev) ?_) ?_
    · refine triple_if_local ge fe f E _ _ _ (!Integers.Int.eq (fc (len - n)) Integers.Int.zero) _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..)),
          boolVal_char _ m⟩) ?_
      rw [hne0]
      exact triple_fallthrough ge fe f _ _ _ _ (triple_skip ge fe f _) (fun _ _ _ x => x)
    · refine triple_seq_fwd ge fe f _ _ _ _ _
        (triple_set_local ge fe f E _ _ _ tb _ _ (fun _ h => h) hn2
          (fun le m hp hT hH hag => hev le m hp
            (TempsHold_mono (fun q hq => List.mem_cons_of_mem _ hq) hT) hH hag)) ?_
      have hmp : ∀ v1 v2, (p, Val.Vptr b o) ∈ (tb, v1) :: (ta, v2) :: (p, Val.Vptr b o) :: l :=
        fun _ _ => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hsubl : ∀ v1 v2, ∀ q ∈ (p, Val.Vptr b o) :: l, q ∈ (tb, v1) :: (ta, v2) :: (p, Val.Vptr b o) :: l :=
        fun _ _ q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)
      refine triple_if_local ge fe f E _ _ _ (Integers.Int.eq (fc (len - n)) (Integers.Int.repr 47)) _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..))) (EvalExpr.Econst_int _ _)
            (cmp47 _ _ m),
          Case5C.boolVal_ofBool_tint _ m⟩) ?_
      cases h47 : Integers.Int.eq (fc (len - n)) (Integers.Int.repr 47)
      · exact triple_fallthrough ge fe f _ _ _ _ (triple_skip ge fe f _)
          (fun e le hp ⟨he, hT, hH⟩ => ⟨fc, o, by omega, hn, ho, ht, he,
            TempsHold_mono (hsubl _ _) hT, hH⟩)
      · refine triple_fallthrough ge fe f _ _ _ _
          (assign_byte ge fe f E _ R _ _ b o fc (len + 1) (len - n) (Integers.Int.repr 92) hpos rfl ho
            (fun le m hT => EvalLvalue.Ederef _ _ b o (EvalExpr.Etempvar _ _ _ (hT.get (hmp _ _))))
            (fun le m hT => ⟨_, EvalExpr.Econst_int _ _, by
              show some (Val.Vint (Integers.Int.sign_ext 8 (Integers.Int.repr 92))) = _
              rw [sext92]⟩))
          (fun e le hp ⟨he, hT, hH⟩ => ⟨upd fc (len - n) (Integers.Int.repr 92), o, by omega, hn, ho,
            tail_upd92 ht hlt, he, TempsHold_mono (hsubl _ _) hT, hH⟩)
  · -- p++
    refine triple_lift ge fe f (fun (x : (Nat → Integers.Int) × Integers.Ptrofs) =>
      fun e le hp => 0 < n ∧ n ≤ len ∧ Integers.Ptrofs.unsigned x.2 = ((len - n : Nat) : _root_.Int)
        ∧ Tail x.1 (len - n) len
        ∧ LocalSt E ((p, .Vptr b x.2) :: l) (arr b x.1 (len + 1) ∗ R) e le hp) _ _ _
      (fun e le hp ⟨fc, o, h⟩ => ⟨(fc, o), h⟩) (fun ⟨fc, o⟩ => ?_)
    refine triple_lift ge fe f (fun (_ : 0 < n ∧ n ≤ len ∧ Integers.Ptrofs.unsigned o = ((len - n : Nat) : _root_.Int)
        ∧ Tail fc (len - n) len) =>
      LocalSt E ((p, .Vptr b o) :: l) (arr b fc (len + 1) ∗ R)) _ _ _
      (fun e le hp ⟨h0, h1, h2, h3, h4⟩ => ⟨⟨h0, h1, h2, h3⟩, h4⟩) (fun ⟨h0, hn, ho, ht⟩ => ?_)
    have hlt : len - n < len := by omega
    have hb := ht.2.2.2.2
    refine triple_fallthrough ge fe f _ _ _ _
      (triple_set_local ge fe f E _ l _ p _ _ (fun q hq => List.mem_cons_of_mem _ hq)
        (fun q hq => (hnl q hq).1)
        (fun le m hp hT _ _ => EvalExpr.Ebinop _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ _ (hT.get (List.mem_cons_self ..))) (EvalExpr.Econst_int _ _)
          (semAdd_ptr_int _ _ _ _ _ rfl)))
      (fun e le hp hL => ⟨n - 1, by omega, fc, _, by omega, ?_, ?_, hL⟩)
    · rw [incr_ofs _ o (len - n) ho (by omega)]
      congr 1
      omega
    · rw [show len - (n - 1) = len - n + 1 by omega]
      exact tail_next ht hlt

/-! ## この関数のための式・構造体・規則 -/

abbrev eData : Expr := .Etempvar _data (tptr (Ty.Tstruct _Curl_easy noattr))

/-- `data->state.up.path` -/
abbrev upPathE : Expr :=
  .Efield (.Efield (.Efield (.Ederef eData (Ty.Tstruct _Curl_easy noattr)) _state
    (Ty.Tstruct _UrlState noattr)) _up (Ty.Tstruct _urlpieces noattr)) _path (tptr tschar)

/-- `smbc->share` -/
abbrev shareE : Expr :=
  .Efield (.Ederef (.Etempvar _smbc (tptr (Ty.Tstruct _smb_conn noattr))) (Ty.Tstruct _smb_conn noattr))
    _share (tptr tschar)

/-- `req->path` -/
abbrev reqPathE : Expr :=
  .Efield (.Ederef (.Etempvar _req (tptr (Ty.Tstruct _smb_request noattr)))
    (Ty.Tstruct _smb_request noattr)) _path (tptr tschar)

def coOf (id : Ident) : Composite :=
  match prog.prog_comp_env.get id with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem co_easy : prog.prog_comp_env.get _Curl_easy = some (coOf _Curl_easy) := rfl
theorem co_us : prog.prog_comp_env.get _UrlState = some (coOf _UrlState) := rfl
theorem co_up : prog.prog_comp_env.get _urlpieces = some (coOf _urlpieces) := rfl
theorem co_conn : prog.prog_comp_env.get _smb_conn = some (coOf _smb_conn) := rfl
theorem co_req : prog.prog_comp_env.get _smb_request = some (coOf _smb_request) := rfl

theorem off_state : fieldOffset prog.prog_comp_env _state (coOf _Curl_easy).co_members = .OK (0, .Full) := by
  decide
theorem off_up : fieldOffset prog.prog_comp_env _up (coOf _UrlState).co_members = .OK (0, .Full) := by
  decide
theorem off_path : fieldOffset prog.prog_comp_env _path (coOf _urlpieces).co_members = .OK (0, .Full) := by
  decide
theorem off_share : fieldOffset prog.prog_comp_env _share (coOf _smb_conn).co_members = .OK (0, .Full) := by
  decide
theorem off_rpath : fieldOffset prog.prog_comp_env _path (coOf _smb_request).co_members = .OK (0, .Full) := by
  decide

theorem lv_upPath {ge : CGenv} {E : Env} {le : TempEnv} {m : Mem} {b : Block} {o : Integers.Ptrofs}
    (hcenv : ge.genv_cenv = prog.prog_comp_env) (hle : le.get _data = some (.Vptr b o)) :
    EvalLvalue ge E le m upPathE b o .Full := by
  have := lv_field (e := E) (m := m) (fld := _path) (ty := tptr tschar)
    (EvalExpr.Elvalue _ _ _ .Full _
      (lv_field (fld := _up) (ty := Ty.Tstruct _urlpieces noattr)
        (EvalExpr.Elvalue _ _ _ .Full _
          (lv_field (fld := _state) (ty := Ty.Tstruct _UrlState noattr) (eval_deref_temp hle) rfl
            (hcenv ▸ co_easy) (hcenv ▸ off_state))
          (DerefLoc.copy rfl))
        rfl (hcenv ▸ co_us) (hcenv ▸ off_up))
      (DerefLoc.copy rfl))
    rfl (hcenv ▸ co_up) (hcenv ▸ off_path)
  simp only [ptrofs_add_zero] at this; exact this

theorem lv_share {ge : CGenv} {E : Env} {le : TempEnv} {m : Mem} {b : Block} {o : Integers.Ptrofs}
    (hcenv : ge.genv_cenv = prog.prog_comp_env) (hle : le.get _smbc = some (.Vptr b o)) :
    EvalLvalue ge E le m shareE b o .Full := by
  have := lv_field (e := E) (m := m) (fld := _share) (ty := tptr tschar) (eval_deref_temp hle) rfl
    (hcenv ▸ co_conn) (hcenv ▸ off_share)
  simp only [ptrofs_add_zero] at this; exact this

theorem lv_reqPath {ge : CGenv} {E : Env} {le : TempEnv} {m : Mem} {b : Block} {o : Integers.Ptrofs}
    (hcenv : ge.genv_cenv = prog.prog_comp_env) (hle : le.get _req = some (.Vptr b o)) :
    EvalLvalue ge E le m reqPathE b o .Full := by
  have := lv_field (e := E) (m := m) (fld := _path) (ty := tptr tschar) (eval_deref_temp hle) rfl
    (hcenv ▸ co_req) (hcenv ▸ off_rpath)
  simp only [ptrofs_add_zero] at this; exact this

/-- セルの読み出し（所有の中のどこかにある `mapsto`）。 -/
theorem cell_load {H R : HProp} {b : Block} {o : Z} {v : Val} {hp : Heap} {m : Mem}
    (heq : H = mapsto Mptr .Freeable b o v ∗ R) (hH : H hp) (hag : Heap.Agrees hp m) (hv : IsPtr v) :
    Mem.load Mptr m b o = some v := by
  rw [heq] at hH
  obtain ⟨h1, h2, _, rfl, hm, _⟩ := hH
  rw [mapsto_load (by decide) hm (Heap.Agrees_union_left hag), loadResult_ptr hv]

theorem eval_load {ge : CGenv} {E : Env} {le : TempEnv} {m : Mem} {a : Expr} {b : Block}
    {o : Integers.Ptrofs} {v : Val} (hlv : EvalLvalue ge E le m a b o .Full)
    (hty : typeof a = tptr tschar) (hl : Mem.load Mptr m b (Integers.Ptrofs.unsigned o) = some v) :
    EvalExpr ge E le m a v :=
  EvalExpr.Elvalue _ b o .Full _ hlv (DerefLoc.value Mptr _ (by rw [hty]; rfl) hl)

/-- 所有を含意で弱める。 -/
theorem heap_imp (ge fe f) (E : Env) (l : List (Ident × Val)) (H H' : HProp) (s : Stmt)
    (R : Sep.ExitConds) (himp : ∀ hp, H hp → H' hp) (h : Triple ge fe f (LocalSt E l H') s R) :
    Triple ge fe f (LocalSt E l H) s R :=
  triple_conseq ge fe f h (fun _ _ _ ⟨he, hT, hH⟩ => ⟨he, hT, himp _ hH⟩)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

/-- 所有の中の存在と純粋な条件を取り出す。 -/
theorem lift_heap {α : Sort u} (ge fe f) (E : Env) (l : List (Ident × Val)) (A : α → HProp)
    (φ : α → Prop) (K : HProp) (s : Stmt) (R : Sep.ExitConds)
    (h : ∀ x, φ x → Triple ge fe f (LocalSt E l (A x ∗ K)) s R) :
    Triple ge fe f (LocalSt E l ((fun hp => ∃ x, φ x ∧ A x hp) ∗ K)) s R := by
  intro k e le hp hf m hd hag hP
  obtain ⟨he, hT, h1, h2, hd12, heq, ⟨x, hx, hA⟩, hK⟩ := hP
  exact h x hx k e le hp hf m hd hag ⟨he, hT, h1, h2, hd12, heq, hA, hK⟩

theorem lift_or (ge fe f) (E : Env) (l : List (Ident × Val)) (A B K : HProp) (s : Stmt)
    (R : Sep.ExitConds)
    (ha : Triple ge fe f (LocalSt E l (A ∗ K)) s R) (hb : Triple ge fe f (LocalSt E l (B ∗ K)) s R) :
    Triple ge fe f (LocalSt E l ((fun hp => A hp ∨ B hp) ∗ K)) s R := by
  intro k e le hp hf m hd hag hP
  obtain ⟨he, hT, h1, h2, hd12, heq, hAB, hK⟩ := hP
  rcases hAB with hA | hB
  · exact ha k e le hp hf m hd hag ⟨he, hT, h1, h2, hd12, heq, hA, hK⟩
  · exact hb k e le hp hf m hd hag ⟨he, hT, h1, h2, hd12, heq, hB, hK⟩

/-- 呼び出しの結果（存在）を取り出す。 -/
theorem lift_ret (ge fe f) (E : Env) (l : List (Ident × Val)) (id : Ident) (Q : Val → HProp)
    (K : HProp) (s : Stmt) (R : Sep.ExitConds)
    (h : ∀ v, Triple ge fe f (LocalSt E (setLocal l id v) (Q v ∗ K)) s R) :
    Triple ge fe f (fun e le hp => ∃ v, LocalSt E (setLocal l id v) (Q v ∗ K) e le hp) s R :=
  triple_lift ge fe f _ s R _ (fun _ _ _ h => h) h

/-- `do { body } while(0)`（`Curl_safefree` の展開）。 -/
theorem once_loop (ge fe f) (P Q : Sep.Assn) (s : Stmt) (h : Triple ge fe f P s (.only Q)) :
    Triple ge fe f P (.Sloop s .Sbreak) (.only Q) :=
  Sep.triple_loop ge fe f (.only Q) (fun _ => P) (fun _ => Q) s .Sbreak
    (fun _ => triple_conseq ge fe f h (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim))
    (fun _ => triple_conseq ge fe f (triple_break ge fe f Q) (fun _ _ _ x => x)
      (fun _ _ _ x => x.elim) (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)) 0

theorem ownStr_ptr {v : Val} {h : Heap} (hv : ownStr v h) : IsPtr v := by
  rcases hv with ⟨rfl, _⟩ | ⟨b, _, _, rfl, _⟩
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl ⟨_, _, rfl⟩

theorem notbool_null {m : Mem} :
    Cop.semUnaryOperation .Onotbool nullV (tptr tschar) m = some (Val.ofBool true) := rfl

theorem notbool_ptr {b : Block} {o : Integers.Ptrofs} {m : Mem}
    (hv : Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) :
    Cop.semUnaryOperation .Onotbool (.Vptr b o) (tptr tschar) m = some (Val.ofBool false) := by
  simp only [Cop.semUnaryOperation, Cop.semNotbool, Cop.boolVal, hv]
  rfl

theorem unsigned_zero : Integers.Ptrofs.unsigned Integers.Ptrofs.zero = ((0 : Nat) : _root_.Int) := by
  rw [ptrofs_unsigned_zero]; rfl

/-! ## 入口の状態・外部関数・局所変数 -/

/-- 関数が読むメモリ。構造体はどれもフィールド1つ（オフセット 0）に減らしてある。 -/
structure Ctx where
  dataB : Block
  dataO : Integers.Ptrofs
  smbcB : Block
  smbcO : Integers.Ptrofs
  reqB : Block
  reqO : Integers.Ptrofs
  upV : Val    -- data->state.up.path
  oldV : Val   -- 入口の smbc->share
  reqV : Val   -- 入口の req->path

def cD (c : Ctx) : HProp := mapsto Mptr .Freeable c.dataB (Integers.Ptrofs.unsigned c.dataO) c.upV
def cS (c : Ctx) (v : Val) : HProp := mapsto Mptr .Freeable c.smbcB (Integers.Ptrofs.unsigned c.smbcO) v
def cR (c : Ctx) (v : Val) : HProp := mapsto Mptr .Freeable c.reqB (Integers.Ptrofs.unsigned c.reqO) v
def cP (bp : Block) (v : Val) : HProp := mapsto Mptr .Freeable bp 0 v

/-- 入口の所有: `data->state.up.path`、`smbc->share` とその文字列（NULL でもよい）、`req->path`。 -/
def H0 (c : Ctx) : HProp := cD c ∗ cS c c.oldV ∗ ownStr c.oldV ∗ cR c c.reqV

abbrev Lb (c : Ctx) : List (Ident × Val) :=
  [(_req, .Vptr c.reqB c.reqO), (_smbc, .Vptr c.smbcB c.smbcO), (_data, .Vptr c.dataB c.dataO)]

/-- 呼ばれる側の関数（記号・型・仕様）。 -/
structure Ext (ge : CGenv) : Prop where
  ud : ∃ b fd, Genv.findSymbol ge.genv_genv _Curl_urldecode = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr tschar, tulong, tptr (tptr tschar), tptr tulong, tint] tint cc_default
    ∧ ∀ bp vs, SatisfiesAt ge (FunctionEntry2 ge) fd (udSpec bp) vs
  dup : ∃ b fd, Genv.findSymbol ge.genv_genv _Curl_cstrdup = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr tschar] (tptr tschar) cc_default
    ∧ ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fd dupSpec vs
  free : ∃ b fd, Genv.findSymbol ge.genv_genv _Curl_cfree = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr tvoid] tvoid cc_default
    ∧ ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fd freeSpec vs
  chr : ∃ b fd, Genv.findSymbol ge.genv_genv _strchr = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr tschar, tint] (tptr tschar) cc_default
    ∧ ∀ sb f n vs, SatisfiesAt ge (FunctionEntry2 ge) fd (chrSpec sb f n) vs
  fail : ∃ b fd, Genv.findSymbol ge.genv_genv _Curl_failf = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr (Ty.Tstruct _Curl_easy noattr), tptr tschar] tvoid
        { cc_vararg := some 2, cc_unproto := false, cc_structret := false }
    ∧ ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fd failSpec vs
  lit : ∃ b, Genv.findSymbol ge.genv_genv ___stringlit_1 = some b

def envP (bp : Block) : Env := emptyEnv.set _path (bp, tptr tschar)

theorem blocks_envP (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (bp : Block) :
    blocksOfEnv ge.genv_cenv (envP bp) = [(bp, 0, 8)] := by
  rw [hcenv]; rfl

/-- 局所変数 `path` を解放して return する。 -/
theorem ret_here (ge fe f) (hcenv : ge.genv_cenv = prog.prog_comp_env) (bp : Block)
    (l : List (Ident × Val)) (Hk : HProp) (a : Expr) (v v' : Val) (Ret : Val → HProp) (Q : Sep.Assn)
    (hev : ∀ le m hp, TempsHold l le → (Hk ∗ Case3C.Locs [(bp, 8)]) hp → Heap.Agrees hp m →
      EvalExpr ge (envP bp) le m a v)
    (hcast : ∀ m, Cop.semCast v (typeof a) f.fn_return m = some v')
    (hret : ∀ hp, Hk hp → Ret v' hp) :
    Triple ge fe f (LocalSt (envP bp) l (Hk ∗ Case3C.Locs [(bp, 8)])) (.Sreturn (some a)) (RR Ret Q) :=
  triple_conseq ge fe f
    (Case3C.ret_locs ge fe f (envP bp) l Hk [(bp, 8)] a v v' Ret hev hcast
      (by rw [blocks_envP ge hcenv bp]; intro x hx; simp at hx; subst hx; exact ⟨bp, 8, rfl, by simp⟩)
      (by rw [blocks_envP ge hcenv bp]; simp) hret)
    (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

theorem temps_weak (ge fe f) (E : Env) (l l' : List (Ident × Val)) (H : HProp) (s : Stmt)
    (R : Sep.ExitConds) (hsub : ∀ q ∈ l', q ∈ l) (h : Triple ge fe f (LocalSt E l' H) s R) :
    Triple ge fe f (LocalSt E l H) s R :=
  triple_conseq ge fe f h (fun _ _ _ ⟨he, hT, hH⟩ => ⟨he, TempsHold_mono hsub hT, hH⟩)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

theorem lift_pure (ge fe f) (E : Env) (l : List (Ident × Val)) (φ : Prop) (A K : HProp) (s : Stmt)
    (R : Sep.ExitConds) (h : φ → Triple ge fe f (LocalSt E l (A ∗ K)) s R) :
    Triple ge fe f (LocalSt E l ((⌜φ⌝ ∗ A) ∗ K)) s R := by
  intro k e le hp hf m hd hag hP
  obtain ⟨he, hT, h1, h2, hd12, heq, hA, hK⟩ := hP
  obtain ⟨hφ, hA'⟩ := pure_sep_elim hA
  exact h hφ k e le hp hf m hd hag ⟨he, hT, h1, h2, hd12, heq, hA', hK⟩

theorem strAt_arr {b : Block} {f : Nat → Integers.Int} {n : Nat} {h : Heap} (hs : strAt b f n h) :
    Tail f 0 n ∧ arr b f (n + 1) h := pure_sep_elim hs

/-- `path` の読み出し（局所変数のセル）。 -/
theorem eval_pathvar {ge : CGenv} {le : TempEnv} {m : Mem} {bp : Block} {v : Val} {H R : HProp}
    {hp : Heap} (heq : H = cP bp v ∗ R) (hH : H hp) (hag : Heap.Agrees hp m) (hv : IsPtr v) :
    EvalExpr ge (envP bp) le m (.Evar _path (tptr tschar)) v := by
  refine EvalExpr.Elvalue _ bp Integers.Ptrofs.zero .Full _ (eval_var_local rfl)
    (DerefLoc.value Mptr _ rfl ?_)
  show Mem.load Mptr m bp (Integers.Ptrofs.unsigned Integers.Ptrofs.zero) = some v
  rw [ptrofs_unsigned_zero]
  exact cell_load heq hH hag hv

/-- 文字列の位置 `i` の文字（`strAt` から）。 -/
theorem eval_char_str {ge : CGenv} {E : Env} {le : TempEnv} {m : Mem} {p : Ident} {b : Block}
    {o : Integers.Ptrofs} {fc : Nat → Integers.Int} {n i : Nat} {H R : HProp} {hp : Heap}
    (hle : le.get p = some (.Vptr b o)) (ho : Integers.Ptrofs.unsigned o = (i : _root_.Int))
    (heq : H = strAt b fc n ∗ R) (hH : H hp) (hag : Heap.Agrees hp m) (hi : i ≤ n) :
    EvalExpr ge E le m (.Ederef (.Etempvar p (tptr tschar)) tschar) (.Vint (fc i)) := by
  rw [heq] at hH
  obtain ⟨h1, h2, _, rfl, hs, _⟩ := hH
  obtain ⟨ht, hA⟩ := strAt_arr hs
  exact eval_char hle ho hA (Heap.Agrees_union_left hag) (by omega) ht.2.2.2.1

theorem valid_str {b : Block} {fc : Nat → Integers.Int} {n i : Nat} {H R : HProp} {hp : Heap} {m : Mem}
    (heq : H = strAt b fc n ∗ R) (hH : H hp) (hag : Heap.Agrees hp m) (hi : i ≤ n) :
    Mem.weakValidPointer m b (i : _root_.Int) = true := by
  rw [heq] at hH
  obtain ⟨h1, h2, _, rfl, hs, _⟩ := hH
  exact arr_valid (strAt_arr hs).2 (Heap.Agrees_union_left hag) (by omega)

theorem cast_bool (x : Bool) (m : Mem) :
    Cop.semCast (Val.ofBool x) tint tbool m = some (Val.ofBool x) := by
  cases x <;> rfl

theorem cmp92 (ce : CompositeEnv) (c : Integers.Int) (m : Mem) :
    Cop.semBinaryOperation ce .Oeq (.Vint c) tschar (.Vint (Integers.Int.repr 92)) tint m
      = some (Val.ofBool (Integers.Int.eq c (Integers.Int.repr 92))) := rfl

theorem vint_inj {r : Integers.Int} (h : Val.Vint r = Val.Vint Integers.Int.zero) : r = Integers.Int.zero := by
  cases h; rfl

/-- 存在を保ったまま1文を進める。 -/
theorem ex_map {α : Sort u} (ge fe f) (P Q : α → Sep.Assn) (s : Stmt)
    (h : ∀ x, Triple ge fe f (P x) s (.only (Q x))) :
    Triple ge fe f (fun e le hp => ∃ x, P x e le hp) s (.only (fun e le hp => ∃ x, Q x e le hp)) := by
  intro k e le hp hf m hd hag ⟨x, hx⟩
  obtain ⟨o, hp', hs, hd', hag', hR⟩ := h x k e le hp hf m hd hag hx
  refine ⟨o, hp', hs, hd', hag', ?_⟩
  cases o <;> first | exact ⟨x, hR⟩ | exact hR

end Deb2026_3805C
