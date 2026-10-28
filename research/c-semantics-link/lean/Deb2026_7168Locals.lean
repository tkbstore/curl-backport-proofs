/-
CVE-2026-7168 で使う道具: ローカル変数を2つ持つ関数（`char *u`・`char *p`。`&u` を取るので CompCert ではメモリに置かれる）の
入口と `return`。`setopt_cptr_proxy`（上流）と `setopt_cptr`（8.14.1）が該当する。

- 入口（`satisfies_locals2`）: 2つのブロックを新しく確保し、その所有（中身は未定義の 8 バイト）を本体の前提に足す
- `return`（`return_locals2`）: 2つのブロックを解放する。所有はセルの並びの末尾に置いた2つのセル（`lcell`）として持つ
C1 の Case 2（ローカル変数 `match` が1つ）の入口と `return` の証明を、2つの変数に広げたもの。
-/
import Deb2026_8927Witness
import Case2Attach3
open CC CC.Sep CC.HProp
open Deb2026_8927

set_option maxRecDepth 20000

namespace Deb2026_7168

def tyC : Ty := tptr tschar

def envUP (iu ip : Ident) (b1 b2 : Block) : Env := (emptyEnv.set iu (b1, tyC)).set ip (b2, tyC)

/-- ローカル変数のブロック（中身は未定義の 8 バイト）を、セルの並びの要素として表したもの。 -/
def lcell (b : Block) : Deb2026_8927.Cell := ⟨.Mint64, b, 0, .Vundef⟩

theorem cells_append (pm : Permission) (xs ys : List Deb2026_8927.Cell) :
    Cells pm (xs ++ ys) = (Cells pm xs ∗ Cells pm ys) := by
  induction xs with
  | nil => simp only [List.nil_append, Cells, List.map, sepList]; exact (emp_sep_eq _).symm
  | cons x xs ih =>
    simp only [List.cons_append, Cells, List.map, sepList] at ih ⊢
    rw [ih, sep_assoc_eq]

theorem lcells_eq (b1 b2 : Block) :
    Cells .Freeable [lcell b1, lcell b2]
      = (undefBytes .Freeable b1 0 8 ∗ (undefBytes .Freeable b2 0 8 ∗ emp)) := by
  simp only [Cells, List.map, sepList, cellP, lcell]
  rw [← undefBytes_mapsto (chunk := .Mint64) .Freeable b1 0 undefEncoded_Mint64 (by decide),
      ← undefBytes_mapsto (chunk := .Mint64) .Freeable b2 0 undefEncoded_Mint64 (by decide)]
  rfl

theorem ne_of_lt_pos {a b : Block} (h : a < b) : a ≠ b := by
  intro e; subst e; rw [Positive.lt_iff] at h; exact Nat.lt_irrefl _ h

/-- **入口**: ローカル変数を2つ（どちらも `char *`）持つ関数が仕様を満たすこと。本体は、新しい2つのブロック
    `b1`・`b2` について、呼び出し側の所有に2つのセル `lcell b1`・`lcell b2` を足した前提で示せばよい。 -/
theorem satisfies_locals2 (ge : CGenv) (f : Function) (S : FunSpec) (vargs : List Val)
    (iu ip : Ident) (le0 : TempEnv) (cs : List Deb2026_8927.Cell)
    (hvars : f.fn_vars = [(iu, tyC), (ip, tyC)])
    (hnv : listNorepet (varNames f.fn_vars)) (hnp : listNorepet (varNames f.fn_params))
    (hdisj : listDisjoint (varNames f.fn_params) (varNames f.fn_temps))
    (hbind : bindParameterTemps f.fn_params vargs (createUndefTemps f.fn_temps) = some le0)
    (hpre : ∀ hp, S.pre vargs hp → Cells .Freeable cs hp)
    (body : ∀ b1 b2, b1 ≠ b2 → Triple ge (FunctionEntry2 ge) f
        (fun e le hp => e = envUP iu ip b1 b2 ∧ le = le0
          ∧ Cells .Freeable (cs ++ [lcell b1, lcell b2]) hp)
        f.fn_body { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := S.post }) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f) S vargs := by
  refine satisfies_internal ge (FunctionEntry2 ge) f S vargs
    (fun e le hp => ∃ b1 b2, b1 ≠ b2 ∧ e = envUP iu ip b1 b2 ∧ le = le0
      ∧ Cells .Freeable (cs ++ [lcell b1, lcell b2]) hp)
    (fun m hp hf hpr hd hag => ?_)
    (fun k e le hp hf m hd hag ⟨b1, b2, hne, hP⟩ => body b1 b2 hne k e le hp hf m hd hag hP)
  let m1 := (Mem.alloc m 0 8).1
  let m2 := (Mem.alloc m1 0 8).1
  obtain ⟨hl1, hu1⟩ := undefBytes_exists .Freeable m.nextblock 0 8
  obtain ⟨hl2, hu2⟩ := undefBytes_exists .Freeable m1.nextblock 0 8
  have hag1 : Heap.Agrees (Heap.union hp hf) m1 := Heap.Agrees_alloc hag
  have g1 : Heap.Agrees hl1 m1 := undefBytes_agrees_alloc m 8 hu1
  have g2 : Heap.Agrees hl2 m2 := undefBytes_agrees_alloc m1 8 hu2
  have hne : m.nextblock ≠ m1.nextblock := by
    have hc0 := bytesPtsTo_ownsRange _ _ _ _ _ hu1 0 (by simp)
    exact ne_of_lt_pos (Heap.Agrees_validBlock g1 hc0)
  have n1 := Case2C.fresh_none hag
  have n2 := Case2C.fresh_none hag1
  have hpn1 : ∀ o, hp m.nextblock o = none := fun o => by
    have := n1 o; cases e : hp m.nextblock o with
    | none => rfl
    | some x => simp [Heap.union, e] at this
  have hfn1 : ∀ o, hf m.nextblock o = none := fun o => by
    have := n1 o; simp only [Heap.union, hpn1 o] at this; exact this
  have hpn2 : ∀ o, hp m1.nextblock o = none := fun o => by
    have := n2 o; cases e : hp m1.nextblock o with
    | none => rfl
    | some x => simp [Heap.union, e] at this
  have hfn2 : ∀ o, hf m1.nextblock o = none := fun o => by
    have := n2 o; simp only [Heap.union, hpn2 o] at this; exact this
  have hd1 : ∀ (h : Heap), (∀ o, h m.nextblock o = none) → Heap.disjoint h hl1 := by
    intro h hn b' o'
    by_cases hb : b' = m.nextblock
    · subst hb; exact Or.inl (hn o')
    · exact Or.inr (undefBytes_none hu1 b' o' (Or.inl hb))
  have hd2 : ∀ (h : Heap), (∀ o, h m1.nextblock o = none) → Heap.disjoint h hl2 := by
    intro h hn b' o'
    by_cases hb : b' = m1.nextblock
    · subst hb; exact Or.inl (hn o')
    · exact Or.inr (undefBytes_none hu2 b' o' (Or.inl hb))
  have hd12 : Heap.disjoint hl1 hl2 := hd2 hl1 (fun o => undefBytes_none hu1 _ o (Or.inl hne.symm))
  refine ⟨envUP iu ip m.nextblock m1.nextblock, le0, m2, Heap.union hl1 hl2, ?_, ?_, ?_, ?_⟩
  · refine FunctionEntry2.intro hnv hnp hdisj ?_ hbind
    rw [hvars]
    exact AllocVariables.cons _ _ _ _ _ _ _ _ _ (Prod.ext rfl rfl)
      (AllocVariables.cons _ _ _ _ _ _ _ _ _ (Prod.ext rfl rfl) (AllocVariables.nil _ _))
  · refine Heap.disjoint_union_left.mpr ⟨hd, ?_⟩
    exact Heap.disjoint_comm (Heap.disjoint_union_right.mpr ⟨hd1 hf hfn1, hd2 hf hfn2⟩)
  · refine Case5C.agrees_union (Case5C.agrees_union (Heap.Agrees_alloc (Heap.Agrees_alloc
      (Heap.Agrees_union_left hag))) (Case5C.agrees_union (Heap.Agrees_alloc g1) g2))
      (Heap.Agrees_alloc (Heap.Agrees_alloc (Heap.Agrees_union_right hd hag)))
  · refine ⟨m.nextblock, m1.nextblock, hne, rfl, rfl, ?_⟩
    rw [cells_append, lcells_eq]
    refine ⟨hp, Heap.union hl1 hl2,
      Heap.disjoint_union_right.mpr ⟨hd1 hp hpn1, hd2 hp hpn2⟩, rfl, hpre hp hpr, ?_⟩
    exact ⟨hl1, hl2, hd12, rfl, hu1, hl2, Heap.emp, Heap.disjoint_comm (Heap.disjoint_emp_left hl2),
      (Heap.union_emp hl2).symm, hu2, rfl⟩

/-- **`return a;`**: 2つのローカル変数のブロックを解放する。`Ret` は呼び出し側の所有（`cs` のセル）だけで述べる。 -/
theorem return_locals2 (ge : CGenv) (fe : EntryRel) (f : Function) (iu ip : Ident) (b1 b2 : Block) (l : List (Ident × Val))
    (cs : List Deb2026_8927.Cell) (a : Expr) (Ret : Val → HProp) (v v' : Val)
    (hne : b1 ≠ b2)
    (hblocks : ∀ blk ∈ blocksOfEnv ge.genv_cenv (envUP iu ip b1 b2),
      blk = (b1, 0, 8) ∨ blk = (b2, 0, 8))
    (hpw : (blocksOfEnv ge.genv_cenv (envUP iu ip b1 b2)).Pairwise (fun a b => a.1 ≠ b.1))
    (hev : ∀ le m hp, TempsHold l le → Cells .Freeable (cs ++ [lcell b1, lcell b2]) hp →
      Heap.Agrees hp m → EvalExpr ge (envUP iu ip b1 b2) le m a v)
    (hcast : ∀ m : Mem, Cop.semCast v (typeof a) f.fn_return m = some v')
    (hret : ∀ hp, Cells .Freeable cs hp → Ret v' hp) :
    Triple ge fe f (LocalSt (envUP iu ip b1 b2) l (Cells .Freeable (cs ++ [lcell b1, lcell b2])))
      (.Sreturn (some a))
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := Ret } := by
  refine triple_return ge fe f _ Ret a (fun e le hp m hP hag => ?_)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  have hev' := hev le m hp hT hH hag
  rw [cells_append, lcells_eq] at hH
  obtain ⟨hA, hL, hdAL, rfl, hcs, h1, h2', hd12, rfl, hu1, h2, he2, hd2e, rfl, hu2, rfl⟩ := hH
  simp only [Heap.union_emp] at *
  have gL := Heap.Agrees_union_right hdAL hag
  have r1 := undefBytes_rangePerm hu1 (Heap.Agrees_union_left gL)
  have r2 := undefBytes_rangePerm hu2 (Heap.Agrees_union_right hd12 gL)
  obtain ⟨m', hm'⟩ := freeList_isSome_of_rangePerm _ m
    (fun blk hb => by
      rcases hblocks blk hb with rfl | rfl
      · exact r1
      · exact r2) hpw
  refine ⟨v, v', m', hA, hev', hcast m, hm', hret hA hcs, fun hf hd hag' => ?_⟩
  have hd' := Heap.disjoint_union_left.mp hd
  refine ⟨hd'.1, Sep.Agrees_freeList _ m m' hm' ?_ (Case2C.agrees_drop (Heap.disjoint_comm hdAL)
    (hd'.2) (by rw [Heap.union_comm hdAL] at hag'; exact hag'))⟩
  intro blk hb ofs h0 h8
  have hown : (Heap.union h1 h2) blk.1 ofs ≠ none := by
    rcases hblocks blk hb with rfl | rfl
    · have h0' : (0 : Int) ≤ ofs := h0
      have h8' : ofs < (8 : Int) := h8
      obtain ⟨n, rfl⟩ : ∃ n : Nat, ofs = (n : Int) := ⟨ofs.toNat, (Int.toNat_of_nonneg h0').symm⟩
      have := bytesPtsTo_ownsRange _ _ _ _ _ hu1 n (by simp; omega)
      simp only [Int.zero_add] at this
      simp only [Heap.union]; rw [this]; simp
    · have h0' : (0 : Int) ≤ ofs := h0
      have h8' : ofs < (8 : Int) := h8
      obtain ⟨n, rfl⟩ : ∃ n : Nat, ofs = (n : Int) := ⟨ofs.toNat, (Int.toNat_of_nonneg h0').symm⟩
      have := bytesPtsTo_ownsRange _ _ _ _ _ hu2 n (by simp; omega)
      simp only [Int.zero_add] at this
      simp only [Heap.union]
      rw [(hd12 _ (n : Int)).resolve_right (by rw [this]; simp), this]; simp
  have eA : hA blk.1 ofs = none := (hdAL blk.1 ofs).resolve_right hown
  have ef : hf blk.1 ofs = none := (hd'.2 blk.1 ofs).resolve_left hown
  simp [Heap.union, eA, ef]

end Deb2026_7168
