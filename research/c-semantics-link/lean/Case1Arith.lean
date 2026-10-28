/-
Case 1: 長さとポインタの差についての算術（`BitVec` の上で、omega で示す）。
-/
import Case1Spec
open CC

namespace Case1C

theorem lenv (ol : Integers.Ptrofs) (i : Nat) :
    Integers.Int64.add (Integers.Ptrofs.to_int64 (Integers.MI.divs (Integers.Ptrofs.sub (Integers.Ptrofs.add ol (Integers.Ptrofs.repr i)) ol) (Integers.Ptrofs.repr 1))) (Integers.Int64.repr 1)
    = Integers.Int64.repr ((i : Int) + 1) := by
  simp only [Integers.Int64.add, Integers.MI.add, Integers.Ptrofs.to_int64, Integers.MI.divs,
    Integers.Ptrofs.sub, Integers.Ptrofs.add, Integers.MI.sub, Integers.MI.add,
    Integers.Ptrofs.repr, Integers.Int64.repr, Integers.MI.repr]
  rw [show ol + BitVec.ofInt Archi.ptrWordsize (i : Int) - ol = BitVec.ofInt Archi.ptrWordsize (i : Int)
    from by rw [BitVec.add_comm, BitVec.add_sub_cancel]]
  rw [show BitVec.ofInt Archi.ptrWordsize 1 = 1#Archi.ptrWordsize from by decide, BitVec.sdiv_one]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofInt]
  omega

theorem uns_repr (i : Nat) (h : i < 2^64) : Integers.Int64.unsigned (Integers.Int64.repr (i : Int)) = i := by
  simp [Integers.Int64.unsigned, Integers.MI.unsigned, Integers.Int64.repr, Integers.MI.repr]
  exact Int.emod_eq_of_lt (by omega) (by omega)


theorem toNat_repr (n : Nat) (hn : n < 2^64) : (Integers.Int64.repr (n : _root_.Int)).toNat = n := by
  simp only [Integers.Int64.repr, Integers.MI.repr, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt hn

theorem tail_lt (n : Nat) (L : Integers.Int64) (hn : n < 2^64)
    (hL1 : 1 ≤ Integers.Int64.unsigned L)
    (hgt : Integers.Int64.cmpu .Cgt (Integers.Int64.repr n) L = true) :
    tailLen n (Integers.Int64.sub (Integers.Int64.repr n) L) < n := by
  have hr := toNat_repr n hn
  simp only [Integers.Int64.cmpu, Integers.MI.cmpu, Integers.MI.ltu, BitVec.ult,
    decide_eq_true_eq] at hgt
  simp only [Integers.Int64.unsigned, Integers.MI.unsigned] at hL1
  unfold tailLen
  simp only [Integers.Int64.unsigned, Integers.MI.unsigned, Integers.Int64.sub, Integers.MI.sub,
    BitVec.toNat_sub, Int.toNat_natCast] at hgt ⊢
  rw [hr] at hgt ⊢
  have : (2 ^ 64 - L.toNat + n) % 2 ^ 64 = n - L.toNat := by omega
  rw [this]
  have hx : 1 ≤ L.toNat := by exact_mod_cast hL1
  split <;> omega

theorem le_of_ngt (n : Nat) (L : Integers.Int64) (hn : n < 2^64)
    (hgt : Integers.Int64.cmpu .Cgt (Integers.Int64.repr n) L = false) :
    n ≤ (Integers.Int64.unsigned L).toNat := by
  have hr := toNat_repr n hn
  simp only [Integers.Int64.cmpu, Integers.MI.cmpu, Integers.MI.ltu, BitVec.ult,
    decide_eq_false_iff_not] at hgt
  simp only [Integers.Int64.unsigned, Integers.MI.unsigned, Int.toNat_natCast]
  rw [hr] at hgt
  omega

end Case1C
