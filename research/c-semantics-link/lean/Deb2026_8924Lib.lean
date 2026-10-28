/-
CVE-2026-8924（research/backport-proof-debian/cases/CVE-2026-8924.md）: 翻訳単位によらない補題。

- `p + n`（`p` は `char *`・配列、`n` は `size_t`）の番地 `lofs`。添字が小さいときの値
- 局所変数の `char` 配列（256 バイト）の `d` 番目に 1 バイト書くこと（`Arr3`: 前・その 1 バイト・後ろ）
-/
import Deb2025_14524Lib
open CC CC.Sep CC.HProp
open Case3C (CellD cellH Cells)

set_option maxRecDepth 20000

namespace Deb2026_8924

/-- `Cop.semAdd` が `p + n`（`n` は 64 bit）で計算する番地。 -/
def lofs (o : Integers.Ptrofs) (n : Integers.Int64) : Integers.Ptrofs :=
  Integers.Ptrofs.add o (Integers.Ptrofs.mul (Integers.Ptrofs.repr 1) (Integers.Ptrofs.of_int64 n))

theorem semAdd_long (cenv : CompositeEnv) (m : Mem) (b : Block) (o : Integers.Ptrofs)
    (n : Integers.Int64) (t : Ty) (ht : t = tptr tschar ∨ t = tarray tschar 256) :
    Cop.semBinaryOperation cenv .Oadd (.Vptr b o) t (.Vlong n) tulong m = some (.Vptr b (lofs o n)) := by
  rcases ht with rfl | rfl <;> rfl

theorem lofs_zero_unsigned (d : Nat) (h : d < 256) :
    Integers.Ptrofs.unsigned (lofs Integers.Ptrofs.zero (Integers.Int64.repr (d : _root_.Int))) = d := by
  have hw : (2 : Nat) ^ Archi.ptrWordsize = 18446744073709551616 := by
    rw [Archi.ptrWordsize_eq]
  have hz : BitVec.toNat (Integers.Ptrofs.zero : Integers.Ptrofs) = 0 := rfl
  simp only [lofs, Integers.Ptrofs.of_int64, Integers.Ptrofs.add, Integers.Ptrofs.mul,
    Integers.Ptrofs.unsigned, Integers.Ptrofs.repr, hz, Integers.MI.add, Integers.MI.mul,
    Integers.MI.repr, Integers.MI.unsigned,
    BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofInt, hw, u64_toNat_repr, BitVec.toNat_zero]
  have h1 : ((1 : _root_.Int) % ((18446744073709551616 : Nat) : _root_.Int)).toNat = 1 := by omega
  have h2 : (((d % 18446744073709551616 : Nat) : _root_.Int) % ((18446744073709551616 : Nat) : _root_.Int)).toNat = d := by omega
  rw [h1, h2]
  refine congrArg (fun n : Nat => (n : _root_.Int)) ?_
  simp only [BitVec.toNat_zero, Nat.one_mul, Nat.zero_add]
  omega

/-- 256 バイトの配列の `d` 番目だけを値 `v` で持つ形。 -/
def Arr3 (b : Block) (d : Nat) (v : Val) : HProp :=
  anyBytes .Freeable b 0 d ∗ (mapsto .Mint8signed .Freeable b d v ∗
    anyBytes .Freeable b ((d : _root_.Int) + 1) (255 - d))

theorem arr_eq (b : Block) (d : Nat) (hd : d < 256) :
    anyBytes .Freeable b 0 256 = anyBytes .Freeable b 0 d ∗ (anyBytes .Freeable b (d : _root_.Int) 1 ∗
      anyBytes .Freeable b ((d : _root_.Int) + 1) (255 - d)) := by
  have e : (256 : Nat) = d + (1 + (255 - d)) := by omega
  rw [e, anyBytes_split, anyBytes_split, show (0 : _root_.Int) + (d : _root_.Int) = d from by omega,
    show ((1 : Nat) : _root_.Int) = 1 from rfl]

theorem arr_join {b : Block} {d : Nat} {v : Val} {h : Heap} (hd : d < 256) (hA : Arr3 b d v h) :
    anyBytes .Freeable b 0 256 h := by
  rw [arr_eq b d hd]
  obtain ⟨h1, h2, d1, rfl, a1, h3, h4, d2, rfl, m3, a4⟩ := hA
  exact ⟨h1, Heap.union h3 h4, d1, rfl, a1, h3, h4, d2, rfl, Case3C.mapsto_anyBytes m3, a4⟩

/-- 先頭の 1 バイトの窓に `char` を書く。 -/
theorem store_front (ge fe f) (E : Env) (lt : List (Ident × Val)) (R : HProp)
    (b : Block) (ofs : Integers.Ptrofs) (vnew : Val) (a1 a2 : Expr)
    (hacc : accessMode (typeof a1) = .By_value .Mint8signed)
    (hlv : ∀ le m, TempsHold lt le → EvalLvalue ge E le m a1 b ofs .Full)
    (hrhs : ∀ le m, TempsHold lt le →
      ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some vnew) :
    Triple ge fe f (LocalSt E lt (anyBytes .Freeable b (Integers.Ptrofs.unsigned ofs) 1 ∗ R))
      (.Sassign a1 a2)
      (.only (LocalSt E lt (mapsto .Mint8signed .Freeable b (Integers.Ptrofs.unsigned ofs) vnew ∗ R))) := by
  refine Sep.triple_assign_any ge fe f _ _ a1 a2 .Mint8signed .Freeable b ofs rfl hacc
    (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, h1, h2, hd, rfl, ha, hR⟩ := hP
  subst he
  exact ⟨vnew, h1, h2, hd, rfl, ha, by show _ % 1 = 0; exact Int.emod_one _, hlv le m hT,
    hrhs le m hT, fun h1' hm' hd' => ⟨rfl, hT, h1', h2, hd', rfl, hm', hR⟩⟩

theorem conv_in (X S : HProp) (b : Block) (d : Nat) (hd : d < 256) :
    (X ∗ (anyBytes .Freeable b 0 256 ∗ S))
      = anyBytes .Freeable b (d : _root_.Int) 1 ∗ (X ∗ ((anyBytes .Freeable b 0 d ∗
          anyBytes .Freeable b ((d : _root_.Int) + 1) (255 - d)) ∗ S)) := by
  rw [arr_eq b d hd, sep_left_comm_eq (anyBytes .Freeable b 0 d), sep_assoc_eq, sep_left_comm_eq X]

theorem conv_out (X S : HProp) (b : Block) (d : Nat) (v : Val) :
    (mapsto .Mint8signed .Freeable b d v ∗ (X ∗ ((anyBytes .Freeable b 0 d ∗
          anyBytes .Freeable b ((d : _root_.Int) + 1) (255 - d)) ∗ S)))
      = X ∗ (Arr3 b d v ∗ S) := by
  unfold Arr3
  rw [sep_left_comm_eq (mapsto _ _ _ _ _) X, ← sep_assoc_eq (mapsto _ _ _ _ _),
    sep_left_comm_eq (mapsto _ _ _ _ _) (anyBytes .Freeable b 0 d)]

/-- 配列（`X ∗ (配列 ∗ S)` の配列）の `d` 番目に `char` を書く。 -/
theorem store_arr (ge fe f) (E : Env) (lt : List (Ident × Val)) (X S : HProp)
    (b : Block) (ofs : Integers.Ptrofs) (d : Nat) (hd : d < 256) (hofs : Integers.Ptrofs.unsigned ofs = d)
    (vnew : Val) (a1 a2 : Expr)
    (hacc : accessMode (typeof a1) = .By_value .Mint8signed)
    (hlv : ∀ le m, TempsHold lt le → EvalLvalue ge E le m a1 b ofs .Full)
    (hrhs : ∀ le m, TempsHold lt le →
      ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some vnew) :
    Triple ge fe f (LocalSt E lt (X ∗ (anyBytes .Freeable b 0 256 ∗ S))) (.Sassign a1 a2)
      (.only (LocalSt E lt (X ∗ (Arr3 b d vnew ∗ S)))) := by
  have h := store_front ge fe f E lt (X ∗ ((anyBytes .Freeable b 0 d ∗
    anyBytes .Freeable b ((d : _root_.Int) + 1) (255 - d)) ∗ S)) b ofs vnew a1 a2 hacc hlv hrhs
  rw [hofs] at h
  rw [conv_in X S b d hd, ← conv_out X S b d vnew]
  exact h

end Deb2026_8924
