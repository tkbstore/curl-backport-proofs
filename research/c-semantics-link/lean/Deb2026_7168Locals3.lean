/-
CVE-2026-7168 で使う道具（その2）: 8.14.1 の `setopt_cptr` はローカル変数を3つ持つ
（`char all[256]`・`char *u`・`char *p`。どれも `&` を取るか配列なのでメモリに置かれる）。
`Deb2026_7168Locals.lean` の入口と `return` を3つのブロックに広げたもの。所有はセルの並びとは別に、
未定義の中身のバイト列（`undefBytes`）として持つ。
-/
import Deb2026_7168Locals
open CC CC.Sep CC.HProp
open Deb2026_8927

set_option maxRecDepth 20000

namespace Deb2026_7168

def envALL (ia iu ip : Ident) (ta : Ty) (b0 b1 b2 : Block) : Env :=
  ((emptyEnv.set ia (b0, ta)).set iu (b1, tyC)).set ip (b2, tyC)

def L3 (b0 b1 b2 : Block) : HProp :=
  undefBytes .Freeable b0 0 256 ∗ (undefBytes .Freeable b1 0 8 ∗ undefBytes .Freeable b2 0 8)

theorem fresh_disj {hp : Heap} {n : Nat} {b : Block} {hl : Heap} (hu : undefBytes .Freeable b 0 n hl)
    (hn : ∀ o, hp b o = none) : Heap.disjoint hp hl := by
  intro b' o'
  by_cases hb : b' = b
  · subst hb; exact Or.inl (hn o')
  · exact Or.inr (undefBytes_none hu b' o' (Or.inl hb))

theorem none_of_union {h1 h2 : Heap} {b : Block} (hn : ∀ o, (Heap.union h1 h2) b o = none) :
    (∀ o, h1 b o = none) ∧ (∀ o, h2 b o = none) := by
  constructor
  · intro o; have := hn o; cases e : h1 b o with
    | none => rfl
    | some x => simp [Heap.union, e] at this
  · intro o; have := hn o; cases e : h1 b o with
    | none => simp only [Heap.union, e] at this; exact this
    | some x => simp [Heap.union, e] at this

theorem satisfies_locals3 (ge : CGenv) (f : Function) (S : FunSpec) (vargs : List Val)
    (ia iu ip : Ident) (ta : Ty) (le0 : TempEnv) (A : HProp)
    (hsz : sizeof ge.genv_cenv ta = 256)
    (hvars : f.fn_vars = [(ia, ta), (iu, tyC), (ip, tyC)])
    (hnv : listNorepet (varNames f.fn_vars)) (hnp : listNorepet (varNames f.fn_params))
    (hdisj : listDisjoint (varNames f.fn_params) (varNames f.fn_temps))
    (hbind : bindParameterTemps f.fn_params vargs (createUndefTemps f.fn_temps) = some le0)
    (hpre : ∀ hp, S.pre vargs hp → A hp)
    (body : ∀ b0 b1 b2, b0 ≠ b1 → b0 ≠ b2 → b1 ≠ b2 → Triple ge (FunctionEntry2 ge) f
        (fun e le hp => e = envALL ia iu ip ta b0 b1 b2 ∧ le = le0 ∧ (A ∗ L3 b0 b1 b2) hp)
        f.fn_body { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := S.post }) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f) S vargs := by
  refine satisfies_internal ge (FunctionEntry2 ge) f S vargs
    (fun e le hp => ∃ b0 b1 b2, b0 ≠ b1 ∧ b0 ≠ b2 ∧ b1 ≠ b2 ∧ e = envALL ia iu ip ta b0 b1 b2
      ∧ le = le0 ∧ (A ∗ L3 b0 b1 b2) hp)
    (fun m hp hf hpr hd hag => ?_)
    (fun k e le hp hf m hd hag ⟨b0, b1, b2, h01, h02, h12, hP⟩ => body b0 b1 b2 h01 h02 h12 k e le hp hf m hd hag hP)
  let m1 := (Mem.alloc m 0 256).1
  let m2 := (Mem.alloc m1 0 8).1
  let m3 := (Mem.alloc m2 0 8).1
  obtain ⟨hl0, hu0⟩ := undefBytes_exists .Freeable m.nextblock 0 256
  obtain ⟨hl1, hu1⟩ := undefBytes_exists .Freeable m1.nextblock 0 8
  obtain ⟨hl2, hu2⟩ := undefBytes_exists .Freeable m2.nextblock 0 8
  have ag1 : Heap.Agrees (Heap.union hp hf) m1 := Heap.Agrees_alloc hag
  have ag2 : Heap.Agrees (Heap.union hp hf) m2 := Heap.Agrees_alloc ag1
  have g0 : Heap.Agrees hl0 m1 := undefBytes_agrees_alloc m 256 hu0
  have g1 : Heap.Agrees hl1 m2 := undefBytes_agrees_alloc m1 8 hu1
  have g2 : Heap.Agrees hl2 m3 := undefBytes_agrees_alloc m2 8 hu2
  have g0' : Heap.Agrees hl0 m2 := Heap.Agrees_alloc g0
  have lt01 : m.nextblock < m1.nextblock :=
    Heap.Agrees_validBlock g0 (bytesPtsTo_ownsRange _ _ _ _ _ hu0 0 (by simp))
  have lt12 : m1.nextblock < m2.nextblock :=
    Heap.Agrees_validBlock g1 (bytesPtsTo_ownsRange _ _ _ _ _ hu1 0 (by simp))
  have lt02 : m.nextblock < m2.nextblock :=
    Heap.Agrees_validBlock g0' (bytesPtsTo_ownsRange _ _ _ _ _ hu0 0 (by simp))
  have h01 := ne_of_lt_pos lt01
  have h12 := ne_of_lt_pos lt12
  have h02 := ne_of_lt_pos lt02
  obtain ⟨hpn0, hfn0⟩ := none_of_union (Case2C.fresh_none hag)
  obtain ⟨hpn1, hfn1⟩ := none_of_union (Case2C.fresh_none ag1)
  obtain ⟨hpn2, hfn2⟩ := none_of_union (Case2C.fresh_none ag2)
  have d01 : Heap.disjoint hl0 hl1 := fresh_disj hu1 (fun o => undefBytes_none hu0 _ o (Or.inl (Ne.symm h01)))
  have d02 : Heap.disjoint hl0 hl2 := fresh_disj hu2 (fun o => undefBytes_none hu0 _ o (Or.inl (Ne.symm h02)))
  have d12 : Heap.disjoint hl1 hl2 := fresh_disj hu2 (fun o => undefBytes_none hu1 _ o (Or.inl (Ne.symm h12)))
  have dL : ∀ h : Heap, (∀ o, h m.nextblock o = none) → (∀ o, h m1.nextblock o = none) →
      (∀ o, h m2.nextblock o = none) → Heap.disjoint h (Heap.union hl0 (Heap.union hl1 hl2)) :=
    fun h n0 n1 n2 => Heap.disjoint_union_right.mpr ⟨fresh_disj hu0 n0,
      Heap.disjoint_union_right.mpr ⟨fresh_disj hu1 n1, fresh_disj hu2 n2⟩⟩
  refine ⟨envALL ia iu ip ta m.nextblock m1.nextblock m2.nextblock, le0, m3,
    Heap.union hl0 (Heap.union hl1 hl2), ?_, ?_, ?_, ?_⟩
  · refine FunctionEntry2.intro hnv hnp hdisj ?_ hbind
    rw [hvars]
    refine AllocVariables.cons _ _ _ _ _ _ _ _ _ ?_
      (AllocVariables.cons _ _ _ _ _ _ _ _ _ (Prod.ext rfl rfl)
        (AllocVariables.cons _ _ _ _ _ _ _ _ _ (Prod.ext rfl rfl) (AllocVariables.nil _ _)))
    rw [hsz]; exact Prod.ext rfl rfl
  · exact Heap.disjoint_union_left.mpr ⟨hd, Heap.disjoint_comm (dL hf hfn0 hfn1 hfn2)⟩
  · refine Case5C.agrees_union (Case5C.agrees_union
      (Heap.Agrees_alloc (Heap.Agrees_alloc (Heap.Agrees_alloc (Heap.Agrees_union_left hag))))
      (Case5C.agrees_union (Heap.Agrees_alloc (Heap.Agrees_alloc g0))
        (Case5C.agrees_union (Heap.Agrees_alloc g1) g2)))
      (Heap.Agrees_alloc (Heap.Agrees_alloc (Heap.Agrees_alloc (Heap.Agrees_union_right hd hag))))
  · refine ⟨m.nextblock, m1.nextblock, m2.nextblock, h01, h02, h12, rfl, rfl, ?_⟩
    exact ⟨hp, _, dL hp hpn0 hpn1 hpn2, rfl, hpre hp hpr, hl0, _, Heap.disjoint_union_right.mpr ⟨d01, d02⟩,
      rfl, hu0, hl1, hl2, d12, rfl, hu1, hu2⟩

theorem owns_undef {b : Block} {n : Nat} {h : Heap} (hu : undefBytes .Freeable b 0 n h) (ofs : Z)
    (h0 : (0 : Int) ≤ ofs) (hn : ofs < (n : Int)) : h b ofs ≠ none := by
  obtain ⟨k, rfl⟩ : ∃ k : Nat, ofs = (k : Int) := ⟨ofs.toNat, (Int.toNat_of_nonneg h0).symm⟩
  have hn' : (k : Int) < (n : Int) := hn
  have := bytesPtsTo_ownsRange _ _ _ _ _ hu k (by simp; omega)
  simp only [Int.zero_add] at this
  rw [this]; simp

theorem return_locals3 (ge : CGenv) (fe : EntryRel) (f : Function) (ia iu ip : Ident) (ta : Ty)
    (b0 b1 b2 : Block) (l : List (Ident × Val)) (A : HProp) (a : Expr) (Ret : Val → HProp) (v v' : Val)
    (hblocks : ∀ blk ∈ blocksOfEnv ge.genv_cenv (envALL ia iu ip ta b0 b1 b2),
      blk = (b0, 0, 256) ∨ blk = (b1, 0, 8) ∨ blk = (b2, 0, 8))
    (hpw : (blocksOfEnv ge.genv_cenv (envALL ia iu ip ta b0 b1 b2)).Pairwise (fun a b => a.1 ≠ b.1))
    (hev : ∀ le m hp, TempsHold l le → (A ∗ L3 b0 b1 b2) hp →
      Heap.Agrees hp m → EvalExpr ge (envALL ia iu ip ta b0 b1 b2) le m a v)
    (hcast : ∀ m : Mem, Cop.semCast v (typeof a) f.fn_return m = some v')
    (hret : ∀ hp, A hp → Ret v' hp) :
    Triple ge fe f (LocalSt (envALL ia iu ip ta b0 b1 b2) l (A ∗ L3 b0 b1 b2))
      (.Sreturn (some a))
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := Ret } := by
  refine triple_return ge fe f _ Ret a (fun e le hp m hP hag => ?_)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  have hev' := hev le m hp hT hH hag
  obtain ⟨hA, hL, hdAL, rfl, hAp, h0, h12, hd0, rfl, hu0, h1, h2, hd12, rfl, hu1, hu2⟩ := hH
  have gL := Heap.Agrees_union_right hdAL hag
  have r0 := undefBytes_rangePerm hu0 (Heap.Agrees_union_left gL)
  have g12 := Heap.Agrees_union_right hd0 gL
  have r1 := undefBytes_rangePerm hu1 (Heap.Agrees_union_left g12)
  have r2 := undefBytes_rangePerm hu2 (Heap.Agrees_union_right hd12 g12)
  obtain ⟨m', hm'⟩ := freeList_isSome_of_rangePerm _ m
    (fun blk hb => by
      rcases hblocks blk hb with rfl | rfl | rfl
      · exact r0
      · exact r1
      · exact r2) hpw
  refine ⟨v, v', m', hA, hev', hcast m, hm', hret hA hAp, fun hf hd hag' => ?_⟩
  have hd' := Heap.disjoint_union_left.mp hd
  refine ⟨hd'.1, Sep.Agrees_freeList _ m m' hm' ?_ (Case2C.agrees_drop (Heap.disjoint_comm hdAL)
    (hd'.2) (by rw [Heap.union_comm hdAL] at hag'; exact hag'))⟩
  intro blk hb ofs hlo hhi
  have hown : (Heap.union h0 (Heap.union h1 h2)) blk.1 ofs ≠ none := by
    rcases hblocks blk hb with rfl | rfl | rfl
    · have := owns_undef hu0 ofs hlo hhi
      simp only [Heap.union]; cases e : h0 b0 ofs with
      | none => exact absurd e this
      | some x => simp
    · have := owns_undef hu1 ofs hlo hhi
      have e0 : h0 b1 ofs = none := (hd0 b1 ofs).resolve_right (by
        simp only [Heap.union]; cases e : h1 b1 ofs with
        | none => exact absurd e this
        | some x => simp)
      simp only [Heap.union, e0]; cases e : h1 b1 ofs with
      | none => exact absurd e this
      | some x => simp
    · have := owns_undef hu2 ofs hlo hhi
      have e1 : h1 b2 ofs = none := (hd12 b2 ofs).resolve_right this
      have e0 : h0 b2 ofs = none := (hd0 b2 ofs).resolve_right (by
        simp only [Heap.union, e1]; exact this)
      simp only [Heap.union, e0, e1]; exact this
  have eA : hA blk.1 ofs = none := (hdAL blk.1 ofs).resolve_right hown
  have ef : hf blk.1 ofs = none := (hd'.2 blk.1 ofs).resolve_left hown
  simp [Heap.union, eA, ef]

end Deb2026_7168
