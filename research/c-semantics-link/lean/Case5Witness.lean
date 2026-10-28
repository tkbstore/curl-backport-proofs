/-
Case 5: 前提 `H c` を満たすヒープとメモリが実際にあること（P0 が空虚でないこと）。

H5 の P0 の反例（ftp:// の要求が、設定の違う FTPS の接続を再利用する）に当たる値を、
1つのブロック（80 バイト）に置いた具体的なメモリを作る。メモリの中身は `decide` で確かめる。

  オフセット  中身
   0  m->data                 （どこを指してもよい。ブロックの先頭を指す）
   8  m->needle      = &needle（24）
  16  m の may_tls・require_tls = 0
  24  needle->scheme = &nscheme（32）
  32  nscheme->protocol = 1
  48  nscheme->flags    = PROTOPT_SSL_REUSE（1 << 15）。PROTOPT_SSL は立てない
  56  conn->scheme   = &cscheme（64）
  72  cscheme->family   = 1（needle の protocol と同じ族）
-/
import Case5Common
open CC CC.Sep CC.HProp
open Case5_after

set_option maxRecDepth 20000

namespace Case5C

/-! ## 一般の補題 -/

theorem bytes_agrees {b : Block} {p : Permission} {ofs : _root_.Int} {vl : List MemVal}
    {h : Heap} {m : Mem} (hb : bytesPtsTo b p ofs vl h)
    (hm : ∀ i : Nat, i < vl.length →
      PMap.get b m.access (ofs + (i : _root_.Int)) .Cur = some p
      ∧ PMap.get b m.access (ofs + (i : _root_.Int)) .Max = some p
      ∧ ZMap.get (ofs + (i : _root_.Int)) (PMap.get b m.contents) = vl[i]!) :
    Heap.Agrees h m := by
  intro b' o c hc
  have hown := bytesPtsTo_ownsRange b p vl ofs h hb
  by_cases hbb : b' = b
  · subst hbb
    rcases Int.lt_or_le o ofs with hlo | hlo
    · rw [bytesPtsTo_none _ p vl ofs h hb _ o (Or.inr (Or.inl hlo))] at hc
      cases hc
    · rcases Int.lt_or_le o (ofs + (vl.length : _root_.Int)) with hhi | hhi
      · have hi : (o - ofs).toNat < vl.length := by omega
        have ho : ofs + (((o - ofs).toNat : Nat) : _root_.Int) = o := by omega
        have hc' := hown _ hi
        rw [ho, hc] at hc'
        cases hc'
        obtain ⟨h1, h2, h3⟩ := hm _ hi
        rw [ho] at h1 h2 h3
        exact ⟨h1, h2, h3⟩
      · rw [bytesPtsTo_none _ p vl ofs h hb _ o (Or.inr (Or.inr hhi))] at hc
        cases hc
  · rw [bytesPtsTo_none b p vl ofs h hb b' o (Or.inl hbb)] at hc
    cases hc

theorem agrees_union {h1 h2 : Heap} {m : Mem} (a1 : Heap.Agrees h1 m) (a2 : Heap.Agrees h2 m) :
    Heap.Agrees (Heap.union h1 h2) m := by
  intro b o c hc
  unfold Heap.union at hc
  cases h : h1 b o with
  | some c1 => rw [h] at hc; cases hc; exact a1 b o _ h
  | none => rw [h] at hc; exact a2 b o c hc

theorem mapsto_disj {c1 c2 : Chunk} {p : Permission} {b : Block} {o1 o2 : _root_.Int}
    {v1 v2 : Val} {h1 h2 : Heap} (hm1 : mapsto c1 p b o1 v1 h1) (hm2 : mapsto c2 p b o2 v2 h2)
    (hr : o1 + (sizeChunkNat c1 : _root_.Int) ≤ o2 ∨ o2 + (sizeChunkNat c2 : _root_.Int) ≤ o1) :
    Heap.disjoint h1 h2 := by
  intro b' o
  rcases hr with hr | hr
  · rcases Int.lt_or_le o (o1 + (sizeChunkNat c1 : _root_.Int)) with h | h
    · exact Or.inr (mapsto_none hm2 b' o (Or.inr (Or.inl (by omega))))
    · exact Or.inl (mapsto_none hm1 b' o (Or.inr (Or.inr h)))
  · rcases Int.lt_or_le o o1 with h | h
    · exact Or.inl (mapsto_none hm1 b' o (Or.inr (Or.inl h)))
    · exact Or.inr (mapsto_none hm2 b' o (Or.inr (Or.inr (by omega))))

/-- 1つのセル: 整列していれば、`bytesPtsTo` から `mapsto` が作れ、メモリと一致する。 -/
theorem cell {chunk : Chunk} {b : Block} {ofs : _root_.Int} {v : Val} {m : Mem}
    (hal : ofs % alignChunk chunk = 0)
    (hm : ∀ i : Nat, i < (encodeVal chunk v).length →
      PMap.get b m.access (ofs + (i : _root_.Int)) .Cur = some .Freeable
      ∧ PMap.get b m.access (ofs + (i : _root_.Int)) .Max = some .Freeable
      ∧ ZMap.get (ofs + (i : _root_.Int)) (PMap.get b m.contents) = (encodeVal chunk v)[i]!) :
    ∃ h, mapsto chunk .Freeable b ofs v h ∧ Heap.Agrees h m := by
  obtain ⟨h, hb⟩ := bytesPtsTo_exists b .Freeable (encodeVal chunk v) ofs
  exact ⟨h, pure_sep_intro hal hb, bytes_agrees hb hm⟩

/-! ## 具体的なメモリ -/

def bw : Block := Mem.empty.nextblock
def m0 : Mem := (Mem.alloc Mem.empty 0 80).1

def ptr (o : Nat) : Val := .Vptr bw (Integers.Ptrofs.repr o)

def storesW : Option Mem := do
  let m ← Mem.store Mptr m0 bw 0 (ptr 0)
  let m ← Mem.store Mptr m bw 8 (ptr 24)
  let m ← Mem.store .Mint32 m bw 16 (.Vint (Integers.Int.repr 0))
  let m ← Mem.store Mptr m bw 24 (ptr 32)
  let m ← Mem.store .Mint64 m bw 32 (.Vlong (Integers.Int64.repr 1))
  let m ← Mem.store .Mint32 m bw 48 (.Vint (Integers.Int.repr 32768))
  let m ← Mem.store Mptr m bw 56 (ptr 64)
  Mem.store .Mint64 m bw 72 (.Vlong (Integers.Int64.repr 1))

theorem storesW_isSome : storesW.isSome = true := by decide

def mW : Mem := storesW.get storesW_isSome

/-- 反例の値。H5 の `P0` の反例 `⟨false, true, true, true, false, false, false⟩` に写る。 -/
def cW : Ctx where
  connB := bw
  connO := Integers.Ptrofs.repr 56
  mB := bw
  mO := Integers.Ptrofs.repr 0
  dataB := bw
  dataO := Integers.Ptrofs.repr 0
  ndlB := bw
  ndlO := Integers.Ptrofs.repr 24
  nschB := bw
  nschO := Integers.Ptrofs.repr 32
  cschB := bw
  cschO := Integers.Ptrofs.repr 64
  bits := Integers.Int.repr 0
  flags := Integers.Int.repr 32768
  proto := Integers.Int64.repr 1
  fam := Integers.Int64.repr 1
  pm := .Freeable

theorem input_cW : input cW true false = ⟨false, true, true, true, false, false, false⟩ := rfl

theorem cW_cells :
    addr cW.mO 0 = 0 ∧ addr cW.mO 8 = 8 ∧ addr cW.mO 16 = 16 ∧ addr cW.ndlO 0 = 24
    ∧ addr cW.nschO 0 = 32 ∧ addr cW.nschO 16 = 48 ∧ addr cW.connO 0 = 56
    ∧ addr cW.cschO 8 = 72 := by
  decide

/-- **前提 `H cW` を満たすヒープが、具体的なメモリ `mW` の上にある。** -/
theorem H_cW_satisfiable : ∃ hp, H cW hp ∧ Heap.Agrees hp mW := by
  obtain ⟨a0, a8, a16, a24, a32, a48, a56, a72⟩ := cW_cells
  obtain ⟨h1, m1, g1⟩ := cell (chunk := Mptr) (b := bw) (ofs := 0) (v := ptr 0) (m := mW)
    (by decide) (by decide)
  obtain ⟨h2, m2, g2⟩ := cell (chunk := Mptr) (b := bw) (ofs := 8) (v := ptr 24) (m := mW)
    (by decide) (by decide)
  obtain ⟨h3, m3, g3⟩ := cell (chunk := .Mint32) (b := bw) (ofs := 16)
    (v := .Vint (Integers.Int.repr 0)) (m := mW) (by decide) (by decide)
  obtain ⟨h4, m4, g4⟩ := cell (chunk := Mptr) (b := bw) (ofs := 24) (v := ptr 32) (m := mW)
    (by decide) (by decide)
  obtain ⟨h5, m5, g5⟩ := cell (chunk := .Mint64) (b := bw) (ofs := 32)
    (v := .Vlong (Integers.Int64.repr 1)) (m := mW) (by decide) (by decide)
  obtain ⟨h6, m6, g6⟩ := cell (chunk := .Mint32) (b := bw) (ofs := 48)
    (v := .Vint (Integers.Int.repr 32768)) (m := mW) (by decide) (by decide)
  obtain ⟨h7, m7, g7⟩ := cell (chunk := Mptr) (b := bw) (ofs := 56) (v := ptr 64) (m := mW)
    (by decide) (by decide)
  obtain ⟨h8, m8, g8⟩ := cell (chunk := .Mint64) (b := bw) (ofs := 72)
    (v := .Vlong (Integers.Int64.repr 1)) (m := mW) (by decide) (by decide)
  have d78 := mapsto_disj m7 m8 (by decide)
  have d6 : Heap.disjoint h6 (Heap.union h7 h8) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m6 m7 (by decide), mapsto_disj m6 m8 (by decide)⟩
  have d5 : Heap.disjoint h5 (Heap.union h6 (Heap.union h7 h8)) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m5 m6 (by decide),
      Heap.disjoint_union_right.mpr ⟨mapsto_disj m5 m7 (by decide), mapsto_disj m5 m8 (by decide)⟩⟩
  have d4 : Heap.disjoint h4 (Heap.union h5 (Heap.union h6 (Heap.union h7 h8))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m5 (by decide),
      Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m6 (by decide),
        Heap.disjoint_union_right.mpr ⟨mapsto_disj m4 m7 (by decide), mapsto_disj m4 m8 (by decide)⟩⟩⟩
  have d3 : Heap.disjoint h3
      (Heap.union h4 (Heap.union h5 (Heap.union h6 (Heap.union h7 h8)))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m4 (by decide),
      Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m5 (by decide),
        Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m6 (by decide),
          Heap.disjoint_union_right.mpr ⟨mapsto_disj m3 m7 (by decide), mapsto_disj m3 m8 (by decide)⟩⟩⟩⟩
  have d2 : Heap.disjoint h2
      (Heap.union h3 (Heap.union h4 (Heap.union h5 (Heap.union h6 (Heap.union h7 h8))))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m3 (by decide),
      Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m4 (by decide),
        Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m5 (by decide),
          Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m6 (by decide),
            Heap.disjoint_union_right.mpr ⟨mapsto_disj m2 m7 (by decide), mapsto_disj m2 m8 (by decide)⟩⟩⟩⟩⟩
  have d1 : Heap.disjoint h1 (Heap.union h2
      (Heap.union h3 (Heap.union h4 (Heap.union h5 (Heap.union h6 (Heap.union h7 h8)))))) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m2 (by decide),
      Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m3 (by decide),
        Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m4 (by decide),
          Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m5 (by decide),
            Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m6 (by decide),
              Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m7 (by decide), mapsto_disj m1 m8 (by decide)⟩⟩⟩⟩⟩⟩
  refine ⟨_, ?_, agrees_union g1 (agrees_union g2 (agrees_union g3 (agrees_union g4
    (agrees_union g5 (agrees_union g6 (agrees_union g7 g8))))))⟩
  unfold H
  rw [a0, a8, a16, a24, a32, a48, a56, a72]
  exact ⟨_, _, d1, rfl, m1, _, _, d2, rfl, m2, _, _, d3, rfl, m3, _, _, d4, rfl, m4,
    _, _, d5, rfl, m5, _, _, d6, rfl, m6, _, _, d78, rfl, m7, m8⟩

end Case5C
