/-
担当 B で共通に使う道具（その2）: セルの並び `Cells` を満たすヒープが、具体的なメモリの上にあること。
P0（修正前の関数で脆弱性が起きる入力がある）の前提が空虚でないことを示すのに使う。
C1 の Case 5 の `H_cW_satisfiable` と同じ考え方を、並びの長さによらない形にした。
-/
import Deb2026_8927Cells
import Case5Witness
open CC CC.Sep CC.HProp

set_option maxRecDepth 20000

namespace Deb2026_8927

/-- セルが番地 `(b, o)` を含む。 -/
def inCell (x : Cell) (b : Block) (o : Z) : Prop :=
  b = x.b ∧ x.o ≤ o ∧ o < x.o + (sizeChunkNat x.chunk : Z)

/-- 2つのセルが重ならない。 -/
def apart (x y : Cell) : Prop :=
  x.b ≠ y.b ∨ x.o + (sizeChunkNat x.chunk : Z) ≤ y.o ∨ y.o + (sizeChunkNat y.chunk : Z) ≤ x.o

instance (x y : Cell) : Decidable (apart x y) := by unfold apart; infer_instance

theorem cells_owns {pm : Permission} : ∀ {cs : List Cell} {hp : Heap}, Cells pm cs hp →
    ∀ {b : Block} {o : Z} {c : CC.Cell}, hp b o = some c → ∃ x ∈ cs, inCell x b o
  | [], hp, h, b, o, c, hc => by
    simp only [Cells, List.map, sepList, emp] at h
    subst h; cases hc
  | x :: xs, hp, h, b, o, c, hc => by
    simp only [Cells, List.map, sepList] at h
    obtain ⟨h1, h2, _, rfl, hx, hrest⟩ := h
    unfold Heap.union at hc
    cases h1b : h1 b o with
    | some c1 =>
      refine ⟨x, List.Mem.head _, ?_⟩
      by_cases hbb : b = x.b
      · subst hbb
        refine ⟨rfl, ?_, ?_⟩
        · rcases Int.lt_or_le o x.o with hlt | hle
          · rw [mapsto_none hx _ o (Or.inr (Or.inl hlt))] at h1b; cases h1b
          · exact hle
        · rcases Int.lt_or_le o (x.o + (sizeChunkNat x.chunk : Z)) with hlt | hge
          · exact hlt
          · rw [mapsto_none hx _ o (Or.inr (Or.inr hge))] at h1b; cases h1b
      · rw [mapsto_none hx b o (Or.inl hbb)] at h1b; cases h1b
    | none =>
      rw [h1b] at hc
      obtain ⟨y, hy, hin⟩ := cells_owns hrest hc
      exact ⟨y, List.Mem.tail _ hy, hin⟩

theorem cell_disjoint {pm : Permission} {x : Cell} {xs : List Cell} {h1 h2 : Heap}
    (hx : cellP pm x h1) (hrest : Cells pm xs h2) (hap : ∀ y ∈ xs, apart x y) :
    Heap.disjoint h1 h2 := by
  intro b o
  cases h2b : h2 b o with
  | none => exact Or.inr rfl
  | some c =>
    left
    obtain ⟨y, hy, hb, hlo, hhi⟩ := cells_owns hrest h2b
    by_cases hbx : b = x.b
    · subst hbx
      rcases hap y hy with hne | hle | hle
      · exact absurd hb hne
      · exact mapsto_none hx _ o (Or.inr (Or.inr (Int.le_trans hle hlo)))
      · exact mapsto_none hx _ o (Or.inr (Or.inl (Int.lt_of_lt_of_le hhi hle)))
    · exact mapsto_none hx b o (Or.inl hbx)

/-- メモリ `m` の上で、セル `x` の中身と権限がそろっている。 -/
def cellOK (m : Mem) (x : Cell) : Prop :=
  x.o % alignChunk x.chunk = 0 ∧
  ∀ i : Nat, i < (encodeVal x.chunk x.v).length →
    PMap.get x.b m.access (x.o + (i : Z)) .Cur = some .Freeable
    ∧ PMap.get x.b m.access (x.o + (i : Z)) .Max = some .Freeable
    ∧ ZMap.get (x.o + (i : Z)) (PMap.get x.b m.contents) = (encodeVal x.chunk x.v)[i]!

instance (m : Mem) (x : Cell) : Decidable (cellOK m x) := by unfold cellOK; infer_instance

/-- **並びのどのセルもメモリとそろっていて、互いに重ならなければ、並びを満たすヒープがある。** -/
theorem cells_satisfiable (m : Mem) : ∀ (cs : List Cell), (∀ x ∈ cs, cellOK m x) →
    cs.Pairwise apart → ∃ hp, Cells .Freeable cs hp ∧ Heap.Agrees hp m
  | [], _, _ => ⟨Heap.emp, rfl, fun _ _ _ h => by cases h⟩
  | x :: xs, hok, hpw => by
    obtain ⟨hal, hm⟩ := hok x (List.Mem.head _)
    obtain ⟨h1, hx, g1⟩ := Case5C.cell hal hm
    obtain ⟨h2, hrest, g2⟩ := cells_satisfiable m xs (fun y hy => hok y (List.Mem.tail _ hy))
      (List.pairwise_cons.mp hpw).2
    refine ⟨Heap.union h1 h2, ?_, Case5C.agrees_union g1 g2⟩
    simp only [Cells, List.map, sepList]
    exact ⟨h1, h2, cell_disjoint hx hrest (List.pairwise_cons.mp hpw).1, rfl, hx, hrest⟩

end Deb2026_8927
