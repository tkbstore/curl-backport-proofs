/-
Case 3: 値を追うセルの並び `Cells` と、その読み書きの規則。

メモリの形は `Cells l ∗ R`（`l` は値を追うセル、`R` は中身を問わない領域と局所変数）。
`k` 番目のセルを読む・書く規則を、並びの位置 `k` で一度だけ証明しておく。書き込みは `l.set k _` になる。
-/
import Case3Common
import Case2Common
open CC CC.Sep CC.HProp

set_option maxRecDepth 20000

namespace Case3C

/-- 値を追うセル: (chunk, 権限, ブロック, 番地, 値)。 -/
abbrev CellD := Chunk × Permission × Block × Z × Val

def cellH (d : CellD) : HProp := mapsto d.1 d.2.1 d.2.2.1 d.2.2.2.1 d.2.2.2.2

def Cells : List CellD → HProp
  | [] => emp
  | d :: l => cellH d ∗ Cells l

theorem cells_pick : ∀ (l : List CellD) (k : Nat) (hk : k < l.length),
    Cells l = cellH l[k] ∗ Cells (l.eraseIdx k)
  | [], _, hk => absurd hk (Nat.not_lt_zero _)
  | d :: l, 0, _ => rfl
  | d :: l, k + 1, hk => by
      have hk' : k < l.length := by simp at hk; omega
      show cellH d ∗ Cells l = cellH (l[k]'hk') ∗ (cellH d ∗ Cells (l.eraseIdx k))
      rw [cells_pick l k hk', sep_left_comm_eq]

theorem eraseIdx_set {α : Type} : ∀ (l : List α) (k : Nat) (d : α), (l.set k d).eraseIdx k = l.eraseIdx k
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | x :: l, k + 1, d => by
      show x :: (l.set k d).eraseIdx k = x :: l.eraseIdx k
      rw [eraseIdx_set l k d]

/-- `k` 番目のセルを取り出す（残りは `R` とまとめる）。 -/
theorem whole_pick (l : List CellD) (R : HProp) (k : Nat) (hk : k < l.length) :
    (Cells l ∗ R) = cellH l[k] ∗ (Cells (l.eraseIdx k) ∗ R) := by
  rw [cells_pick l k hk, sep_assoc_eq]

theorem cell_load3 {l : List CellD} {R : HProp} {k : Nat} {hk : k < l.length}
    {ch : Chunk} {p : Permission} {b : Block} {o : Z} {v : Val}
    (hl : l[k]'hk = (ch, p, b, o, v)) (hpr : permOrder p .Readable = true)
    {hp : Heap} {m : Mem} (hH : (Cells l ∗ R) hp) (hag : Heap.Agrees hp m) :
    Mem.load ch m b o = some (Val.loadResult ch v) := by
  rw [whole_pick l R k hk, hl] at hH
  obtain ⟨h1, h2, _, rfl, hm, _⟩ := hH
  exact mapsto_load hpr hm (Heap.Agrees_union_left hag)

/-- `k` 番目のセルへの書き込み。 -/
theorem assign_cell3 (ge fe f) (E : Env) (lt : List (Ident × Val)) (l : List CellD) (R : HProp)
    (k : Nat) (hk : k < l.length) (ch : Chunk) (p : Permission) (b : Block) (o : Integers.Ptrofs)
    (vold vnew : Val) (hl : l[k]'hk = (ch, p, b, Integers.Ptrofs.unsigned o, vold))
    (a1 a2 : Expr) (hpw : permOrder p .Writable = true)
    (hacc : accessMode (typeof a1) = .By_value ch)
    (hlv : ∀ le m, TempsHold lt le → EvalLvalue ge E le m a1 b o .Full)
    (hrhs : ∀ le m hp, TempsHold lt le → (Cells l ∗ R) hp → Heap.Agrees hp m →
      ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some vnew) :
    Triple ge fe f (LocalSt E lt (Cells l ∗ R)) (.Sassign a1 a2)
      (.only (LocalSt E lt (Cells (l.set k (ch, p, b, Integers.Ptrofs.unsigned o, vnew)) ∗ R))) := by
  refine triple_assign ge fe f _ _ a1 a2 ch p b o hpw hacc (fun e le hp m hP hag => ?_)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  obtain ⟨v2, hev, hcast⟩ := hrhs le m hp hT hH hag
  rw [whole_pick l R k hk, hl] at hH
  obtain ⟨h1, h2, hd, rfl, hm, hR⟩ := hH
  have hk' : k < (l.set k (ch, p, b, Integers.Ptrofs.unsigned o, vnew)).length := by simpa using hk
  refine ⟨vold, vnew, h1, h2, hd, rfl, hm, hlv le m hT, ⟨v2, hev, hcast⟩, fun h1' hm' hd' => ?_⟩
  refine ⟨rfl, hT, ?_⟩
  rw [whole_pick _ R k hk', List.getElem_set_self, eraseIdx_set]
  exact ⟨h1', h2, hd', rfl, hm', hR⟩

/-- `k` 番目のセル（32 bit の単位）の中の 1 ビットのビットフィールドへの書き込み。 -/
theorem assign_bit3 (ge fe f) (E : Env) (lt : List (Ident × Val)) (l : List CellD) (R : HProp)
    (k : Nat) (hk : k < l.length) (p : Permission) (b : Block) (o : Integers.Ptrofs) (pos : Z)
    (c n : Integers.Int) (hl : l[k]'hk = (.Mint32, p, b, Integers.Ptrofs.unsigned o, .Vint c))
    (a1 a2 : Expr) (hpw : permOrder p .Writable = true) (hpr : permOrder p .Readable = true)
    (hty : typeof a1 = tint) (hpos0 : 0 ≤ pos) (hpos : pos + 1 ≤ 32)
    (hlv : ∀ le m, TempsHold lt le → EvalLvalue ge E le m a1 b o (.Bits .I32 .Unsigned pos 1))
    (hrhs : ∀ le m, TempsHold lt le →
      ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some (.Vint n)) :
    Triple ge fe f (LocalSt E lt (Cells l ∗ R)) (.Sassign a1 a2)
      (.only (LocalSt E lt (Cells (l.set k (.Mint32, p, b, Integers.Ptrofs.unsigned o,
        .Vint (Integers.Int.bitfield_insert (Cop.firstBit .I32 pos 1).toNat 1 c n))) ∗ R))) := by
  refine Case2C.triple_assign_bitfield ge fe f _ _ a1 a2 p b o pos hpw hpr hty hpos0 hpos
    (fun e le hp m hP hag => ?_)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  obtain ⟨v2, hev, hcast⟩ := hrhs le m hT
  rw [whole_pick l R k hk, hl] at hH
  obtain ⟨h1, h2, hd, rfl, hm, hR⟩ := hH
  refine ⟨c, n, h1, h2, hd, rfl, hm, hlv le m hT, ⟨v2, hev, hcast⟩, fun h1' hm' hd' => ?_⟩
  refine ⟨rfl, hT, ?_⟩
  have hk' : k < (l.set k (.Mint32, p, b, Integers.Ptrofs.unsigned o,
      .Vint (Integers.Int.bitfield_insert (Cop.firstBit .I32 pos 1).toNat 1 c n))).length := by
    simpa using hk
  rw [whole_pick _ R k hk', List.getElem_set_self, eraseIdx_set]
  exact ⟨h1', h2, hd', rfl, hm', hR⟩

/-- `mapsto` は、同じ大きさの「中身を問わないバイト列」でもある。 -/
theorem mapsto_anyBytes {ch : Chunk} {p : Permission} {b : Block} {o : Z} {v : Val} {h : Heap}
    (hm : mapsto ch p b o v h) : anyBytes p b o (sizeChunkNat ch) h := by
  obtain ⟨_, hb⟩ := pure_sep_elim hm
  exact ⟨encodeVal ch v, pure_sep_intro (length_encodeVal _ _) hb⟩

end Case3C
