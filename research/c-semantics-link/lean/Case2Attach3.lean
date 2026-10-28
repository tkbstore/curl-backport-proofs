/-
Case 2: `url_attach_existing` の証明の部品（その4）。環境・新しいブロック・ローカル変数の評価・解放。
-/
import Case2Attach2
open CC CC.Sep CC.HProp
open Case2_after
open Case5C (addr bitOf sep_l sep_r)

set_option maxRecDepth 20000

namespace Case2C

def tyM : Ty := Ty.Tstruct _url_conn_match noattr

def envM (b : Block) : Env := emptyEnv.set _match (b, tyM)

theorem envM_get (b : Block) : (envM b).get _match = some (b, tyM) := PTree.gss _ _ _

theorem envM_none (b : Block) (id : Ident) (h : id ≠ _match) : (envM b).get id = none := by
  unfold envM
  rw [PTree.gso _match id _ _ (Ne.symm h)]
  exact PTree.gempty id

/-- `Agrees` する断片は、まだ確保されていないブロックを持たない。 -/
theorem fresh_none {h : Heap} {m : Mem} (hag : Heap.Agrees h m) (o : Z) : h m.nextblock o = none := by
  cases hc : h m.nextblock o with
  | none => rfl
  | some c =>
      have := Heap.Agrees_validBlock hag hc
      exact absurd this (by simp [Positive.lt_iff])

/-! ## ローカル変数 `match` の評価 -/

theorem eval_match {ge : CGenv} {le : TempEnv} {m : Mem} {b : Block} :
    EvalExpr ge (envM b) le m (.Evar _match tyM) (.Vptr b Integers.Ptrofs.zero) :=
  EvalExpr.Elvalue _ b Integers.Ptrofs.zero .Full _
    (EvalLvalue.Evar_local _ b tyM (envM_get b)) (DerefLoc.copy rfl)

theorem lv_match_field {ge : CGenv} {le : TempEnv} {m : Mem} {b : Block} {fld : Ident} {ty : Ty}
    {d : Z} {bf : Bitfield}
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hfld : fieldOffset prog.prog_comp_env fld (coOf _url_conn_match).co_members = .OK (d, bf)) :
    EvalLvalue ge (envM b) le m (.Efield (.Evar _match tyM) fld ty) b
      (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr d)) bf :=
  EvalLvalue.Efield_struct _ fld ty b Integers.Ptrofs.zero _url_conn_match (coOf _url_conn_match) noattr
    d bf eval_match rfl (hcenv ▸ co_match) (hcenv ▸ hfld)

/-- `match.<fld>` の読み出し（`fld` は 1 bit のビットフィールド、単位は 40 バイト目）。 -/
theorem eval_match_bits {ge : CGenv} {le : TempEnv} {m : Mem} {b : Block} {fld : Ident} {pos : Z}
    {w : Integers.Int}
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hfld : fieldOffset prog.prog_comp_env fld (coOf _url_conn_match).co_members
      = .OK (40, .Bits .I32 .Unsigned pos 1))
    (hpos0 : 0 ≤ pos) (hpos : pos + 1 ≤ 32)
    (hload : Mem.load .Mint32 m b 40 = some (.Vint w)) :
    EvalExpr ge (envM b) le m (.Efield (.Evar _match tyM) fld tint)
      (.Vint (Cop.bitfieldExtract .I32 .Unsigned pos 1 w)) :=
  EvalExpr.Elvalue _ b _ (.Bits .I32 .Unsigned pos 1) _ (lv_match_field hcenv hfld)
    (DerefLoc.bitfield .I32 .Unsigned pos 1 _
      (Cop.LoadBitfield.intro .I32 .Signed noattr .Unsigned pos 1 m _ w hpos0 (by decide)
        (by decide) hpos (by decide) (by show Mem.load _ _ _ _ = _; rw [uz40]; exact hload)))

/-! ## `MlocAny` の所有から: 読み出し・解放の許可・持っている範囲 -/

theorem mlocAny_load {b : Block} {w : Integers.Int} {X : HProp} {h : Heap} {m : Mem}
    (hh : (MlocAny b w ∗ X) h) (hag : Heap.Agrees h m) :
    Mem.load .Mint32 m b 40 = some (.Vint w) := by
  obtain ⟨h1, c1, a1⟩ := sep_l hh hag
  obtain ⟨r1, d1, b1⟩ := sep_r c1 a1
  obtain ⟨h2, c2, a2⟩ := sep_l d1 b1
  exact mapsto_load rfl c2 a2

theorem anyBytes_elim {p : Permission} {b : Block} {ofs : _root_.Int} {n : Nat} {h : Heap}
    (ha : anyBytes p b ofs n h) : ∃ bytes, bytes.length = n ∧ bytesPtsTo b p ofs bytes h := by
  obtain ⟨bytes, hb⟩ := ha
  obtain ⟨hl, hbp⟩ := pure_sep_elim hb
  exact ⟨bytes, hl, hbp⟩

theorem mlocAny_rangePerm {b : Block} {w : Integers.Int} {h : Heap} {m : Mem}
    (hh : MlocAny b w h) (hag : Heap.Agrees h m) :
    Mem.rangePerm m b 0 48 .Cur .Freeable = true := by
  obtain ⟨h1, h2, hd, rfl, ha1, h3, h4, hd34, rfl, hw, ha4⟩ := hh
  obtain ⟨l1, hl1, hb1⟩ := anyBytes_elim ha1
  obtain ⟨l4, hl4, hb4⟩ := anyBytes_elim ha4
  have g1 := Heap.Agrees_union_left hag
  have g2 := Heap.Agrees_union_right hd hag
  have g3 := Heap.Agrees_union_left g2
  have g4 := Heap.Agrees_union_right hd34 g2
  have r1 := bytesPtsTo_rangePerm hb1 g1
  rw [hl1] at r1
  rw [mapsto_eq_bytes (by decide)] at hw
  have r3 := bytesPtsTo_rangePerm hw g3
  rw [length_encodeVal] at r3
  have r4 := bytesPtsTo_rangePerm hb4 g4
  rw [hl4] at r4
  exact Mem.rangePerm_append (Mem.rangePerm_append r1 r3) r4

theorem mlocAny_owns {b : Block} {w : Integers.Int} {h : Heap} (hh : MlocAny b w h) (o : _root_.Int)
    (h0 : 0 ≤ o) (h48 : o < 48) : h b o ≠ none := by
  obtain ⟨h1, h2, hd, rfl, ha1, h3, h4, hd34, rfl, hw, ha4⟩ := hh
  obtain ⟨l1, hl1, hb1⟩ := anyBytes_elim ha1
  obtain ⟨l4, hl4, hb4⟩ := anyBytes_elim ha4
  rw [mapsto_eq_bytes (by decide)] at hw
  have o1 := bytesPtsTo_ownsRange _ _ _ _ _ hb1
  have o3 := bytesPtsTo_ownsRange _ _ _ _ _ hw
  have o4 := bytesPtsTo_ownsRange _ _ _ _ _ hb4
  intro hn
  unfold Heap.union at hn
  rcases Int.lt_or_le o 40 with c1 | c1
  · have := o1 o.toNat (by rw [hl1]; omega)
    rw [show (0 : _root_.Int) + ((o.toNat : Nat) : _root_.Int) = o from by omega] at this
    rw [this] at hn
    cases hn
  · cases hh1 : h1 b o with
    | some _ => rw [hh1] at hn; cases hn
    | none =>
      rw [hh1] at hn
      simp only at hn
      rcases Int.lt_or_le o 44 with c3 | c3
      · have := o3 (o - 40).toNat (by rw [length_encodeVal]; show _ < 4; omega)
        rw [show (40 : _root_.Int) + (((o - 40).toNat : Nat) : _root_.Int) = o from by omega] at this
        rw [this] at hn
        cases hn
      · cases hh3 : h3 b o with
        | some _ => rw [hh3] at hn; cases hn
        | none =>
          rw [hh3] at hn
          have := o4 (o - 44).toNat (by rw [hl4]; omega)
          rw [show (44 : _root_.Int) + (((o - 44).toNat : Nat) : _root_.Int) = o from by omega] at this
          rw [this] at hn
          cases hn

/-- 断片の一部（`h1` を除いた残り）と frame の和も、メモリと一致する。 -/
theorem agrees_drop {h1 h2 hf : Heap} {m : Mem} (hd12 : Heap.disjoint h1 h2)
    (hd1f : Heap.disjoint h1 hf)
    (hag : Heap.Agrees (Heap.union (Heap.union h1 h2) hf) m) :
    Heap.Agrees (Heap.union h2 hf) m := by
  intro b o c hc
  refine hag b o c ?_
  cases e1 : h1 b o with
  | none => simp only [Heap.union, e1]; exact hc
  | some c1 =>
      have e2 : h2 b o = none := (hd12 b o).resolve_left (by rw [e1]; simp)
      have ef : hf b o = none := (hd1f b o).resolve_left (by rw [e1]; simp)
      simp only [Heap.union, e2, ef] at hc
      cases hc

end Case2C
