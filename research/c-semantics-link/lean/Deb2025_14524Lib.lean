/-
CVE-2025-14524（research/backport-proof-debian/cases/CVE-2025-14524.md）: 翻訳単位によらない補題。

- `Cells` の連結、隙間なく並んだセルを「中身を問わないバイト列」に戻すこと（局所変数を解放する前に使う）
- `struct SASL` の 28 番地からの 4 バイト: `authused`（16 bit）と、`force_ir` などのビットフィールドの単位（32 bit）が
  同じバイトを使う（CompCert の配置）。ビットフィールドを書いたあと、前半 2 バイトを `authused` のために切り出す
- 呼ばれる側の仕様の形 `specK`（Case 3 と同じ。メモリの形 `K` を受け取り `K'` にして返す）
-/
import Case3Cells
import Case4debAfter
open CC CC.Sep CC.HProp
open Case3C (CellD cellH Cells)
open Case5C (addr)

set_option maxRecDepth 20000

namespace Deb2025_14524

/-- 呼ばれる側の仕様の形: メモリの形 `K` を受け取り、`K'` にして返す。戻り値は `r`（`none` なら問わない）。 -/
def specK (tyargs : List Ty) (tyres : Ty) (cc : CallConv) (K K' : HProp) (r : Option Val) :
    FunSpec where
  tyargs := tyargs
  tyres := tyres
  cc := cc
  pre := fun _ hp => K hp
  post := fun v hp => (∀ x, r = some x → v = x) ∧ K' hp
  measure := fun _ => 0

theorem cells_append : ∀ (l1 l2 : List CellD), Cells (l1 ++ l2) = Cells l1 ∗ Cells l2
  | [], l2 => (emp_sep_eq _).symm
  | d :: l1, l2 => by
      show cellH d ∗ Cells (l1 ++ l2) = (cellH d ∗ Cells l1) ∗ Cells l2
      rw [cells_append l1 l2, sep_assoc_eq]

/-- セルの大きさの合計。 -/
def csize : List CellD → Nat
  | [] => 0
  | d :: l => sizeChunkNat d.1 + csize l

/-- セルが、ブロック `b` の番地 `o` から隙間なく並んでいる（権限はどれも `p`）。 -/
def contig (b : Block) (p : Permission) : Z → List CellD → Prop
  | _, [] => True
  | o, d :: l => d.2.1 = p ∧ d.2.2.1 = b ∧ d.2.2.2.1 = o ∧ contig b p (o + sizeChunkNat d.1) l

theorem cells_anyBytes (b : Block) (p : Permission) :
    ∀ (l : List CellD) (o : Z) (h : Heap), contig b p o l → Cells l h → anyBytes p b o (csize l) h
  | [], o, h, _, hc => by
      show anyBytes p b o 0 h
      rw [anyBytes_zero]; exact hc
  | (ch, p', b', o', v) :: l, o, h, ⟨hp, hb, ho, hr⟩, hc => by
      simp only at hp hb ho
      subst hp hb ho
      obtain ⟨h1, h2, hd, rfl, hm, hl⟩ := hc
      show anyBytes p' b' o' (sizeChunkNat ch + csize l) _
      rw [anyBytes_split]
      exact ⟨h1, h2, hd, rfl, Case3C.mapsto_anyBytes hm, cells_anyBytes b' p' l _ h2 hr hl⟩

/-! ## 28 番地からの 4 バイト -/

/-- 32 bit の単位 `w` の後半 2 バイト。 -/
def hi2 (p : Permission) (b : Block) (o : Z) (w : Integers.Int) : HProp :=
  bytesPtsTo b p (o + 2) ((encodeVal .Mint32 (.Vint w)).drop 2)

theorem word_split {p : Permission} {b : Block} {o : Z} {w : Integers.Int} {h : Heap}
    (hm : mapsto .Mint32 p b o (.Vint w) h) :
    o % 4 = 0 ∧ (anyBytes p b o 2 ∗ hi2 p b o w) h := by
  obtain ⟨hal, hb⟩ := pure_sep_elim hm
  refine ⟨hal, ?_⟩
  rw [show encodeVal .Mint32 (.Vint w)
        = (encodeVal .Mint32 (.Vint w)).take 2 ++ (encodeVal .Mint32 (.Vint w)).drop 2
        from (List.take_append_drop _ _).symm, bytesPtsTo_append] at hb
  obtain ⟨h1, h2, hd, rfl, hb1, hb2⟩ := hb
  have hl : ((encodeVal .Mint32 (.Vint w)).take 2).length = 2 := by
    rw [List.length_take, length_encodeVal]; rfl
  refine ⟨h1, h2, hd, rfl, ⟨_, pure_sep_intro hl hb1⟩, ?_⟩
  unfold hi2
  rw [hl] at hb2
  exact hb2

/-- 先頭の 32 bit の単位の中の 1 ビットのビットフィールドへの書き込み。 -/
theorem bitstore_front (ge fe f) (E : Env) (l : List (Ident × Val)) (R : HProp) (p : Permission)
    (b : Block) (ofs : Integers.Ptrofs) (pos : Z) (w n : Integers.Int) (a1 a2 : Expr)
    (hpw : permOrder p .Writable = true) (hpr : permOrder p .Readable = true)
    (hty : typeof a1 = tint) (hpos0 : 0 ≤ pos) (hpos : pos + 1 ≤ 32)
    (hlv : ∀ le m, TempsHold l le → EvalLvalue ge E le m a1 b ofs (.Bits .I32 .Unsigned pos 1))
    (hrhs : ∀ le m, TempsHold l le →
      ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some (.Vint n)) :
    Triple ge fe f (LocalSt E l (mapsto .Mint32 p b (Integers.Ptrofs.unsigned ofs) (.Vint w) ∗ R))
      (.Sassign a1 a2)
      (.only (LocalSt E l (mapsto .Mint32 p b (Integers.Ptrofs.unsigned ofs)
        (.Vint (Integers.Int.bitfield_insert (Cop.firstBit .I32 pos 1).toNat 1 w n)) ∗ R))) := by
  refine Case2C.triple_assign_bitfield ge fe f _ _ a1 a2 p b ofs pos hpw hpr hty hpos0 hpos
    (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, h1, h2, hd, rfl, hM, hR⟩ := hP
  subst he
  exact ⟨w, n, h1, h2, hd, rfl, hM, hlv le m hT, hrhs le m hT,
    fun h1' hm' hd' => ⟨rfl, hT, h1', h2, hd', rfl, hm', hR⟩⟩

/-- 先頭の 32 bit の単位の前半 2 バイトへの 16 bit の書き込み（`sasl->authused = …`）。 -/
theorem store16_word (ge fe f) (E : Env) (l : List (Ident × Val)) (R : HProp) (p : Permission)
    (b : Block) (ofs : Integers.Ptrofs) (w : Integers.Int) (v : Val) (a1 a2 : Expr)
    (hpw : permOrder p .Writable = true)
    (hacc : accessMode (typeof a1) = .By_value .Mint16unsigned)
    (hlv : ∀ le m, TempsHold l le → EvalLvalue ge E le m a1 b ofs .Full)
    (hrhs : ∀ le m, TempsHold l le →
      ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some v) :
    Triple ge fe f (LocalSt E l (mapsto .Mint32 p b (Integers.Ptrofs.unsigned ofs) (.Vint w) ∗ R))
      (.Sassign a1 a2)
      (.only (LocalSt E l ((mapsto .Mint16unsigned p b (Integers.Ptrofs.unsigned ofs) v
        ∗ hi2 p b (Integers.Ptrofs.unsigned ofs) w) ∗ R))) := by
  refine Sep.triple_assign_any ge fe f _ _ a1 a2 .Mint16unsigned p b ofs hpw hacc
    (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, h1, h2, hd, rfl, hM, hR⟩ := hP
  subst he
  obtain ⟨hal, hA, hHi, dAH, rfl, ha, hhi⟩ := word_split hM
  have hd' := Heap.disjoint_union_left.mp hd
  refine ⟨v, hA, Heap.union hHi h2, Heap.disjoint_union_right.mpr ⟨dAH, hd'.1⟩,
    Heap.union_assoc _ _ _, ha,
    by rw [show alignChunk .Mint16unsigned = 2 from rfl,
         ← Int.emod_emod_of_dvd _ (by decide : (2 : _root_.Int) ∣ 4),
         show Integers.Ptrofs.unsigned ofs % 4 = 0 from hal]; rfl,
    hlv le m hT, hrhs le m hT, fun h1' hm' hd1 => ?_⟩
  have hd1' := Heap.disjoint_union_right.mp hd1
  refine ⟨rfl, hT, Heap.union h1' hHi, h2, Heap.disjoint_union_left.mpr ⟨hd1'.2, hd'.2⟩,
    (Heap.union_assoc _ _ _).symm, ⟨h1', hHi, hd1'.1, rfl, hm', hhi⟩, hR⟩

/-- 4 バイトの列から 32 bit を読む。 -/
theorem bytes_load32 {p : Permission} {b : Block} {o : Z} {bytes : List MemVal} {h : Heap} {m : Mem}
    (hpr : permOrder p .Readable = true) (hal : o % 4 = 0) (hlen : bytes.length = 4)
    (hb : bytesPtsTo b p o bytes h) (hag : Heap.Agrees h m) :
    Mem.load .Mint32 m b o = some (decodeVal .Mint32 bytes) := by
  have hown := bytesPtsTo_ownsRange b p bytes o h hb
  have hrp := Heap.Agrees_rangePerm hag hown .Cur
  rw [hlen] at hrp
  have hva : Mem.validAccess m .Mint32 b o .Readable = true := by
    simp only [Mem.validAccess, Bool.and_eq_true]
    exact ⟨Mem.rangePerm_implies hrp hpr, by simp [alignChunk, hal]⟩
  unfold Mem.load
  rw [hva]
  simp only [if_true]
  congr 1
  rw [show Mem.getN (sizeChunkNat .Mint32) o (PMap.get b m.contents) = bytes from ?_]
  rw [show sizeChunkNat .Mint32 = bytes.length from hlen.symm]
  exact Heap.Agrees_getN hag bytes o hown

/-- `authused`（`au`）を書いたあとに 28 番地から読む 32 bit の値。 -/
def w16x (au w : Integers.Int) : Integers.Int :=
  Integers.Int.repr (decodeInt (encodeInt 2 (Integers.Int.unsigned au)
    ++ (encodeInt 4 (Integers.Int.unsigned w)).drop 2))

/-- `authused` を書いたあとでも、28 番地から 32 bit を読むと `w16x au w` になる。 -/
theorem word16_load {p : Permission} {b : Block} {o : Z} {au w : Integers.Int} {h : Heap} {m : Mem}
    (hpr : permOrder p .Readable = true) (hal : o % 4 = 0)
    (hH : (mapsto .Mint16unsigned p b o (.Vint au) ∗ hi2 p b o w) h) (hag : Heap.Agrees h m) :
    Mem.load .Mint32 m b o = some (.Vint (w16x au w)) := by
  obtain ⟨h1, h2, hd, rfl, hm, hhi⟩ := hH
  obtain ⟨_, hb1⟩ := pure_sep_elim hm
  have hl1 : (encodeVal .Mint16unsigned (.Vint au)).length = 2 := by rw [length_encodeVal]; rfl
  have hb : bytesPtsTo b p o (encodeVal .Mint16unsigned (.Vint au)
      ++ (encodeVal .Mint32 (.Vint w)).drop 2) (Heap.union h1 h2) := by
    rw [bytesPtsTo_append, hl1]
    exact ⟨h1, h2, hd, rfl, hb1, hhi⟩
  have hlen : (encodeVal .Mint16unsigned (.Vint au) ++ (encodeVal .Mint32 (.Vint w)).drop 2).length
      = 4 := by
    rw [List.length_append, hl1, List.length_drop, length_encodeVal]; rfl
  rw [bytes_load32 hpr hal hlen hb hag]
  show some (decodeVal .Mint32 (injBytes (encodeInt 2 (Integers.Int.unsigned au))
    ++ (injBytes (encodeInt 4 (Integers.Int.unsigned w))).drop 2)) = _
  rw [injBytes, injBytes, ← List.map_drop, ← List.map_append, ← injBytes]
  simp only [decodeVal, projBytes_injBytes]
  rfl

/-- `R` の中の `mapsto` への書き込み（`Cells l ∗ ((mapsto … ∗ Q) ∗ S)` の形）。 -/
theorem store_in_R (ge fe f) (E : Env) (lt : List (Ident × Val)) (l : List CellD) (Q S : HProp)
    (ch : Chunk) (p : Permission) (b : Block) (ofs : Integers.Ptrofs) (vold vnew : Val) (a1 a2 : Expr)
    (hpw : permOrder p .Writable = true) (hacc : accessMode (typeof a1) = .By_value ch)
    (hlv : ∀ le m, TempsHold lt le → EvalLvalue ge E le m a1 b ofs .Full)
    (hrhs : ∀ le m, TempsHold lt le →
      ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some vnew) :
    Triple ge fe f
      (LocalSt E lt (Cells l ∗ ((mapsto ch p b (Integers.Ptrofs.unsigned ofs) vold ∗ Q) ∗ S)))
      (.Sassign a1 a2)
      (.only (LocalSt E lt (Cells l ∗ ((mapsto ch p b (Integers.Ptrofs.unsigned ofs) vnew ∗ Q) ∗ S)))) := by
  refine Sep.triple_assign ge fe f _ _ a1 a2 ch p b ofs hpw hacc (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  rw [sep_left_comm_eq, sep_assoc_eq] at hH
  obtain ⟨h1, h2, hd, rfl, hm, hR⟩ := hH
  refine ⟨vold, vnew, h1, h2, hd, rfl, hm, hlv le m hT, hrhs le m hT, fun h1' hm' hd' => ?_⟩
  refine ⟨rfl, hT, ?_⟩
  rw [sep_left_comm_eq, sep_assoc_eq]
  exact ⟨h1', h2, hd', rfl, hm', hR⟩

theorem bitOf_nz {w : Integers.Int} {pos : Z} (h : Case5C.bitOf w pos = true) :
    Integers.Int.eq (Cop.bitfieldExtract .I32 .Unsigned pos 1 w) Integers.Int.zero = false := by
  unfold Case5C.bitOf at h; revert h; cases Integers.Int.eq _ _ <;> simp

theorem cast_bool_nz {x : Integers.Int} (hx : Integers.Int.eq x Integers.Int.zero = false) (m : Mem) :
    Cop.semCast (.Vint x) tint tbool m = some (Val.ofBool true) := by
  show some (.Vint (if Integers.Int.eq x Integers.Int.zero then Integers.Int.zero else Integers.Int.one))
    = some (Val.ofBool true)
  rw [hx]; rfl

/-! ## 値の補題 -/

theorem zext16_idem (x : Integers.Int) :
    Integers.Int.zero_ext 16 (Integers.Int.zero_ext 16 x) = Integers.Int.zero_ext 16 x := by
  show Integers.MI.zero_ext 16 (Integers.MI.zero_ext 16 x) = Integers.MI.zero_ext 16 x
  apply BitVec.eq_of_toNat_eq
  rw [toNat_zero_ext_16, toNat_zero_ext_16, Nat.mod_mod]

theorem boolVal_ofBool_int (b : Bool) (m : Mem) : Cop.boolVal (Val.ofBool b) tint m = some b := by
  cases b <;> rfl

/-- 追っている一時変数の一部を捨てる。 -/
theorem weaken (ge fe f) {P : Sep.Assn} {s : Stmt} {E : Env} {l l' : List (Ident × Val)}
    {Hh : HProp}
    (h : Triple ge fe f P s (.only (LocalSt E l Hh))) (hsub : ∀ p ∈ l', p ∈ l) :
    Triple ge fe f P s (.only (LocalSt E l' Hh)) :=
  triple_conseq ge fe f h (fun _ _ _ x => x)
    (fun _ _ _ ⟨he, hT, hH⟩ => ⟨he, TempsHold_mono hsub hT, hH⟩)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

/-- 事前条件のメモリの形を、同じものの別の書き方に取り替える。 -/
theorem pre_conv (ge fe f) {s : Stmt} {R : Sep.ExitConds} {E : Env} {l : List (Ident × Val)}
    {H1 H2 : HProp} (hconv : ∀ hp, H1 hp → H2 hp)
    (h : Triple ge fe f (LocalSt E l H2) s R) : Triple ge fe f (LocalSt E l H1) s R :=
  triple_conseq ge fe f h (fun _ _ _ ⟨he, hT, hH⟩ => ⟨he, hT, hconv _ hH⟩)
    (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)

macro "ptget" : tactic =>
  `(tactic| repeat (first
      | exact PTree.gss _ _ _
      | refine (PTree.gso _ _ _ _ (by decide)).trans ?_))

/-- `∀ p ∈ l', p ∈ l`（`l'` は具体的な短い並び、`l` は `setLocal` の連鎖）。 -/
macro "subt" : tactic =>
  `(tactic| (intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp;
             rcases hp with h | h | h | h | h | h | h <;> (subst_vars; temps_get)))

/-! ## 呼び出しの規則（呼ばれる側がメモリの形 `K` を受け取り `K'` にして返す） -/

theorem callK_none (ge fe f) (tyargs : List Ty) (tyres : Ty) (cc : CallConv) (K K' : HProp)
    (r : Option Val) (callee : Expr) (al : List Expr) (E : Env) (l : List (Ident × Val))
    (vargs : List Val) (fb : Block) (fd : FunDef)
    (hspec : ∀ vs, SatisfiesAt ge fe fd (specK tyargs tyres cc K K' r) vs)
    (hfind : FuncPtr ge fb fd) (hty : typeOfFundef fd = .Tfunction tyargs tyres cc)
    (hclass : Cop.classifyFun (typeof callee) = .f tyargs tyres cc)
    (hcallee : ∀ le m, TempsHold l le → EvalExpr ge E le m callee (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge E le m al tyargs vargs) :
    Triple ge fe f (LocalSt E l K) (.Scall none callee al) (.only (LocalSt E l K')) := by
  refine Sep.triple_call ge fe f (specK tyargs tyres cc K K' r) none callee al _ _ fb fd hspec hfind
    hty hclass (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, hK⟩ := hP
  subst he
  refine ⟨vargs, hp, Heap.emp, Heap.disjoint_emp_right hp, (Heap.union_emp hp).symm,
    hcallee le m hT, hargs le m hT, hK, ?_⟩
  intro v h1' hpost _
  rw [Heap.union_emp]
  exact ⟨rfl, hT, hpost.2⟩

/-- 戻り値を一時変数 `id` に受ける呼び出し。仕様の `pre` は引数を問わない形でなくてもよい（`hpre`）。 -/
theorem callS_some (ge fe f) (S : FunSpec) (K K' : HProp) (vret : Val) (id : Ident)
    (callee : Expr) (al : List Expr) (E : Env) (l : List (Ident × Val))
    (vargs : List Val) (fb : Block) (fd : FunDef)
    (hspec : ∀ vs, SatisfiesAt ge fe fd S vs)
    (hfind : FuncPtr ge fb fd) (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun (typeof callee) = .f S.tyargs S.tyres S.cc)
    (hcallee : ∀ le m, TempsHold l le → EvalExpr ge E le m callee (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge E le m al S.tyargs vargs)
    (hpre : ∀ hp, K hp → S.pre vargs hp)
    (hpost : ∀ v hp, S.post v hp → v = vret ∧ K' hp) :
    Triple ge fe f (LocalSt E l K) (.Scall (some id) callee al)
      (.only (LocalSt E (setLocal l id vret) K')) := by
  refine Sep.triple_call ge fe f S (some id) callee al _ _ fb fd hspec hfind hty hclass
    (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, hK⟩ := hP
  subst he
  refine ⟨vargs, hp, Heap.emp, Heap.disjoint_emp_right hp, (Heap.union_emp hp).symm,
    hcallee le m hT, hargs le m hT, hpre hp hK, ?_⟩
  intro v h1' hS _
  obtain ⟨rfl, hK'⟩ := hpost v h1' hS
  rw [Heap.union_emp]
  exact ⟨rfl, TempsHold_set (fun _ hq => (mem_dropId hq).2)
    (TempsHold_mono (fun _ hq => (mem_dropId hq).1) hT), hK'⟩

theorem boolVal_ptr {b : Block} {o : Integers.Ptrofs} {m : Mem} (t : Ty) (ht : t = tptr tschar)
    (hv : Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) :
    Cop.boolVal (.Vptr b o) t m = some true := by
  subst ht
  simp only [Cop.boolVal, hv]
  rfl

theorem cast_bool_ptr {b : Block} {o : Integers.Ptrofs} {m : Mem}
    (hv : Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) :
    Cop.semCast (.Vptr b o) (tptr tschar) tbool m = some (.Vint Integers.Int.one) := by
  simp only [Cop.semCast, hv]
  rfl

/-- セルのうち 1 バイトのものから、ポインタが有効であることを言う。 -/
theorem cell_valid {l : List CellD} {R : HProp} {k : Nat} {hk : k < l.length}
    {p : Permission} {b : Block} {o : Integers.Ptrofs} {v : Val}
    (hl : l[k]'hk = (.Mint8unsigned, p, b, Integers.Ptrofs.unsigned o, v))
    (hpn : permOrder p .Nonempty = true)
    {hp : Heap} {m : Mem} (hH : (Cells l ∗ R) hp) (hag : Heap.Agrees hp m) :
    Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true := by
  rw [Case3C.whole_pick l R k hk, hl] at hH
  obtain ⟨h1, h2, _, rfl, hm, _⟩ := hH
  exact Case4debC.mapsto_weakValid hpn hm (Heap.Agrees_union_left hag)
    (by show 0 < sizeChunkNat .Mint8unsigned; decide)

/-! ## 読み書きするメモリ（U・D で共通。構造体の配置は前置きが同じなので同じ） -/

structure Ctx where
  sB : Block                 -- sasl
  sO : Integers.Ptrofs
  dB : Block                 -- data
  dO : Integers.Ptrofs
  pB : Block                 -- progress
  pO : Integers.Ptrofs
  cB : Block                 -- data->conn
  cO : Integers.Ptrofs
  uB : Block                 -- data->state.aptr.user（NULL でない）
  uO : Integers.Ptrofs
  uch : Integers.Int         -- 利用者名の先頭のバイト（ポインタが有効であることを言うために所有する）
  bset : Bool                -- data->set.str[STRING_BEARER] が NULL でないか
  bB : Block
  bO : Integers.Ptrofs
  bch : Integers.Int         -- Bearer の文字列の先頭のバイト
  cuV : Val                  -- conn->user
  am : Integers.Int          -- sasl->authmechs
  pf : Integers.Int          -- sasl->prefmech
  sw : Integers.Int          -- sasl の 28 番地からの 32 bit（authused と force_ir などのビットフィールド）
  prv : Integers.Int         -- *progress
  setw : Integers.Int        -- data->set の allow_auth_to_other_hosts（ビット 0）・sasl_ir（ビット 1）の単位
  stw : Integers.Int         -- data->state の this_is_a_follow（ビット 0）の単位
  pm : Permission

def bearerV (c : Ctx) : Val :=
  if c.bset then .Vptr c.bB c.bO else .Vlong (Integers.Int64.repr 0)

/-- `data->set.str[STRING_BEARER]` の番地（添字 56）。 -/
def strOfs (o : Integers.Ptrofs) : Integers.Ptrofs :=
  Integers.Ptrofs.add
    (Integers.Ptrofs.add (Integers.Ptrofs.add o (Integers.Ptrofs.repr 8)) (Integers.Ptrofs.repr 0))
    (Integers.Ptrofs.mul (Integers.Ptrofs.repr 8) (Cop.ptrofsOfInt .Signed (Integers.Int.repr 56)))

/-- enabledmechs に入る値（`sasl->authmechs & sasl->prefmech` を unsigned short にしたもの）。 -/
def em (c : Ctx) : Integers.Int :=
  Integers.Int.zero_ext 16
    (Integers.Int.and (Integers.Int.zero_ext 16 c.am) (Integers.Int.zero_ext 16 c.pf))

/-- `force_ir` を書いたあとの 32 bit の単位。 -/
def swF (c : Ctx) (fir : Bool) : Integers.Int :=
  Integers.Int.bitfield_insert (Cop.firstBit .I32 18 1).toNat 1 c.sw
    (if fir then Integers.Int.one else Integers.Int.zero)

/-- 値を追う、関数の外のセル（`prv` は `*progress` の値）。 -/
abbrev outer (c : Ctx) (prv : Integers.Int) : List CellD :=
  [(.Mint16unsigned, c.pm, c.sB, addr c.sO 24, .Vint c.am),
   (.Mint16unsigned, c.pm, c.sB, addr c.sO 26, .Vint c.pf),
   (.Mint32, c.pm, c.pB, Integers.Ptrofs.unsigned c.pO, .Vint prv),
   (Mptr, c.pm, c.dB, addr c.dO 0, .Vptr c.cB c.cO),
   (Mptr, c.pm, c.dB, Integers.Ptrofs.unsigned (strOfs c.dO), bearerV c),
   (.Mint32, c.pm, c.dB, addr (Integers.Ptrofs.add c.dO (Integers.Ptrofs.repr 8)) 560, .Vint c.setw),
   (Mptr, c.pm, c.dB,
     addr (Integers.Ptrofs.add (Integers.Ptrofs.add c.dO (Integers.Ptrofs.repr 576))
       (Integers.Ptrofs.repr 0)) 0, .Vptr c.uB c.uO),
   (.Mint32, c.pm, c.dB, addr (Integers.Ptrofs.add c.dO (Integers.Ptrofs.repr 576)) 8, .Vint c.stw),
   (Mptr, c.pm, c.cB, addr c.cO 0, c.cuV),
   (.Mint8unsigned, c.pm, c.uB, Integers.Ptrofs.unsigned c.uO, .Vint c.uch),
   (.Mint8unsigned, c.pm, c.bB, Integers.Ptrofs.unsigned c.bO, .Vint c.bch)]

/-- `authused`（値 `au`）と、ビットフィールドの単位の後半 2 バイト。 -/
def SW2 (c : Ctx) (fir : Bool) (au : Integers.Int) : HProp :=
  mapsto .Mint16unsigned c.pm c.sB (addr c.sO 28) (.Vint au) ∗ hi2 c.pm c.sB (addr c.sO 28) (swF c fir)

end Deb2025_14524
