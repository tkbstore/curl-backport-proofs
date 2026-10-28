/-
CVE-2025-10148（research/backport-proof-debian/cases/CVE-2025-10148.md）: 4つの証明（U1・U0・D1・D0）で共通に使う部分。

- `struct ws_encoder` の所有（入口と出口）。`firstbyte`（オフセット 24、1バイト）と `contfragment`（オフセット 24 の 32 bit 単位の 8 bit 目）は
  同じバイトに重なるので、24〜27 の4バイトは、ビットフィールドを読み書きする間は `mapsto .Mint32`、それより後は `anyBytes` として持つ
- 本体を区切る `sp`・`hdS` と、区切りをつなぐ `chain`
- 書き込みだけのセル（`anyBytes`）への代入、`head[k]` への代入、式の評価のタクティク
-/
import GenDeb2025_10148UpAfter
import Deb2026_3805After
import Case2Common
open CC CC.Sep CC.HProp
open Deb2025_10148_up_after
open Case5C (RR)
open Case4debC (IsPtr cast_ptr)

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Deb2025_10148C

/-! ## 本体の区切り -/

/-- 文の並び（右に入れ子の `Ssequence`）の `n` 番目から後ろ。 -/
def sp : Nat → Stmt → Stmt
  | 0, s => s
  | n + 1, .Ssequence _ r => sp n r
  | _, _ => .Sskip

/-- 並びの先頭の文。 -/
def hdS : Stmt → Stmt
  | .Ssequence a _ => a
  | s => s

/-- `n` 番目の文を示し、その後ろへつなぐ。 -/
theorem chain (ge fe f) (B : Stmt) (i : Nat) (P Q : Sep.Assn) (Ret : Val → HProp) (Q' : Sep.Assn)
    (hs : sp i B = .Ssequence (hdS (sp i B)) (sp (i + 1) B))
    (h1 : Triple ge fe f P (hdS (sp i B)) (RR Ret Q))
    (h2 : Triple ge fe f Q (sp (i + 1) B) (RR Ret Q')) :
    Triple ge fe f P (sp i B) (RR Ret Q') := by
  rw [hs]
  exact triple_seq ge fe f P Q (RR Ret Q') _ _ h1 h2

theorem only_RR (ge fe f) {P Q : Sep.Assn} {s : Stmt} (Ret : Val → HProp)
    (h : Triple ge fe f P s (.only Q)) : Triple ge fe f P s (RR Ret Q) :=
  triple_conseq ge fe f h (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x.elim)
    (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)

/-! ## 所有の言い換え -/

theorem mapsto_anyB {chunk : Chunk} {b : Block} {o : Z} {v : Val} {h : Heap}
    (hm : mapsto chunk .Freeable b o v h) : anyBytes .Freeable b o (sizeChunkNat chunk) h := by
  obtain ⟨_, hb⟩ := pure_sep_elim hm
  have := anyBytes_of_bytesPtsTo hb
  rwa [length_encodeVal] at this

theorem bytes_anyB {b : Block} {o : Z} {l : List MemVal} {n : Nat} {h : Heap}
    (hl : l.length = n) (hb : bytesPtsTo b .Freeable o l h) : anyBytes .Freeable b o n h :=
  hl ▸ anyBytes_of_bytesPtsTo hb

theorem sep_imp_l {P P' R : HProp} {h : Heap} (hi : ∀ h, P h → P' h) (hs : (P ∗ R) h) : (P' ∗ R) h := by
  obtain ⟨h1, h2, hd, he, hp, hr⟩ := hs
  exact ⟨h1, h2, hd, he, hi _ hp, hr⟩

instance instAssocSep : Std.Associative (α := HProp) (· ∗ ·) := ⟨sep_assoc_eq⟩
instance instCommSep : Std.Commutative (α := HProp) (· ∗ ·) := ⟨sep_comm_eq⟩

/-- `anyBytes` の窓から、位置 `k` の `len` バイトを取り出す（前と後ろは残す）。 -/
theorem any3 (b : Block) (o : Z) (k len r : Nat) :
    anyBytes .Freeable b o (k + (len + r))
      = anyBytes .Freeable b (o + k) len ∗ (anyBytes .Freeable b o k ∗ anyBytes .Freeable b (o + k + len) r) := by
  rw [anyBytes_split _ _ o k, anyBytes_split _ _ _ len r]
  ac_rfl

/-! ## 規則 -/

/-- 書き込むだけのセル（中身は問わない）への代入。代入の後も `anyBytes` として持つ。 -/
theorem store_any (ge fe f) (E : Env) (l : List (Ident × Val)) (R : HProp)
    (a1 a2 : Expr) (chunk : Chunk) (b : Block) (ofs : Integers.Ptrofs) (o : Z)
    (hacc : accessMode (typeof a1) = .By_value chunk)
    (ho : Integers.Ptrofs.unsigned ofs = o) (hal : o % alignChunk chunk = 0)
    (hlv : ∀ le m, TempsHold l le → EvalLvalue ge E le m a1 b ofs .Full)
    (hev : ∀ le m, TempsHold l le →
      ∃ v2 vnew, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some vnew) :
    Triple ge fe f (LocalSt E l (anyBytes .Freeable b o (sizeChunkNat chunk) ∗ R)) (.Sassign a1 a2)
      (.only (LocalSt E l (anyBytes .Freeable b o (sizeChunkNat chunk) ∗ R))) := by
  subst ho
  refine triple_assign_any ge fe f _ _ a1 a2 chunk .Freeable b ofs (by decide) hacc
    (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, h1, h2, hd, heq, hm, hr⟩ := hP
  subst he
  obtain ⟨v2, vnew, hev2, hc⟩ := hev le m hT
  exact ⟨vnew, h1, h2, hd, heq, hm, hal, hlv le m hT, ⟨v2, hev2, hc⟩,
    fun h1' hm' hd' => ⟨rfl, hT, h1', h2, hd', rfl, mapsto_anyB hm', hr⟩⟩

/-- 1バイトの窓（大きな `anyBytes` の中の位置 `k`）への代入。 -/
theorem store_byte (ge fe f) (E : Env) (l : List (Ident × Val)) (R : HProp)
    (a1 a2 : Expr) (b : Block) (ofs : Integers.Ptrofs) (o : Z) (k r : Nat)
    (hacc : accessMode (typeof a1) = .By_value .Mint8unsigned)
    (ho : Integers.Ptrofs.unsigned ofs = o + k)
    (hlv : ∀ le m, TempsHold l le → EvalLvalue ge E le m a1 b ofs .Full)
    (hev : ∀ le m, TempsHold l le →
      ∃ v2 vnew, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some vnew) :
    Triple ge fe f (LocalSt E l (anyBytes .Freeable b o (k + (1 + r)) ∗ R)) (.Sassign a1 a2)
      (.only (LocalSt E l (anyBytes .Freeable b o (k + (1 + r)) ∗ R))) := by
  rw [any3 b o k 1 r, sep_assoc_eq]
  exact store_any ge fe f E l _ a1 a2 .Mint8unsigned b ofs (o + k) hacc ho (by simp [alignChunk])
    hlv hev

/-- ビットフィールド（32 bit の単位の `pos` 目の1ビット）への代入。単位の中身は存在で持ち直す。 -/
theorem store_bit (ge fe f) (E : Env) (l : List (Ident × Val)) (R : HProp)
    (a1 a2 : Expr) (b : Block) (ofs : Integers.Ptrofs) (o pos : Z) (c : Integers.Int)
    (hty : typeof a1 = tint) (hpos0 : 0 ≤ pos) (hpos : pos + 1 ≤ 32)
    (ho : Integers.Ptrofs.unsigned ofs = o)
    (hlv : ∀ le m, TempsHold l le → EvalLvalue ge E le m a1 b ofs (.Bits .I32 .Unsigned pos 1))
    (hev : ∀ le m, TempsHold l le →
      ∃ v2 n, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some (.Vint n)) :
    Triple ge fe f (LocalSt E l (mapsto .Mint32 .Freeable b o (.Vint c) ∗ R)) (.Sassign a1 a2)
      (.only (fun e le hp => ∃ c', LocalSt E l (mapsto .Mint32 .Freeable b o (.Vint c') ∗ R) e le hp)) := by
  subst ho
  refine Case2C.triple_assign_bitfield ge fe f _ _ a1 a2 .Freeable b ofs pos (by decide) (by decide)
    hty hpos0 hpos (fun e le hp m hP _ => ?_)
  obtain ⟨he, hT, h1, h2, hd, heq, hm, hr⟩ := hP
  subst he
  obtain ⟨v2, n, hev2, hc⟩ := hev le m hT
  exact ⟨c, n, h1, h2, hd, heq, hm, hlv le m hT, ⟨v2, hev2, hc⟩,
    fun h1' hm' hd' => ⟨_, rfl, hT, h1', h2, hd', rfl, hm', hr⟩⟩

/-- `if (a) …` で、条件の値が分かっている枝へ進む（`triple_if_local` を、評価だけを渡す形にしたもの）。 -/
theorem if_val (ge fe f) (E : Env) (l : List (Ident × Val)) (H : HProp)
    (a : Expr) (bb : Bool) (s1 s2 : Stmt) (R : Sep.ExitConds) (v : Val)
    (hev : ∀ le m hp, TempsHold l le → H hp → Heap.Agrees hp m → EvalExpr ge E le m a v)
    (hb : ∀ m, Cop.boolVal v (typeof a) m = some bb)
    (h : Triple ge fe f (LocalSt E l H) (if bb then s1 else s2) R) :
    Triple ge fe f (LocalSt E l H) (.Sifthenelse a s1 s2) R :=
  triple_if_local ge fe f E l H a bb s1 s2 R (fun le m hp hT hH hag => ⟨v, hev le m hp hT hH hag, hb m⟩) h

/-- 何もしない枝（`Sskip`）で、次の前提へ移る。 -/
theorem skip_to (ge fe f) (P Q : Sep.Assn) (Ret : Val → HProp) (h : ∀ e le hp, P e le hp → Q e le hp) :
    Triple ge fe f P .Sskip (RR Ret Q) :=
  triple_conseq ge fe f (triple_skip ge fe f P) (fun _ _ _ x => x) h (fun _ _ _ x => x.elim)
    (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)

/-! ## 式の評価 -/

/-- `Etempvar` は並びから、定数はそのまま、演算とキャストは中を評価してから `rfl`。 -/
syntax "ev" : tactic
macro_rules
  | `(tactic| ev) => `(tactic| first
      | exact EvalExpr.Econst_int _ _
      | exact EvalExpr.Etempvar _ _ _ ((‹TempsHold _ _›).get (by lmem))
      | (refine EvalExpr.Ecast _ _ _ _ ?_ ?_
         · ev
         · rfl)
      | (refine EvalExpr.Ebinop _ _ _ _ _ _ _ ?_ ?_ ?_
         · ev
         · ev
         · rfl)
      | (refine EvalExpr.Eunop _ _ _ _ _ ?_ ?_
         · ev
         · rfl))

/-! ## 構造体 `ws_encoder` -/

def coEnc : Composite :=
  match prog.prog_comp_env.get _ws_encoder with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }

theorem co_enc : prog.prog_comp_env.get _ws_encoder = some coEnc := rfl
theorem off_pl : fieldOffset prog.prog_comp_env _payload_len coEnc.co_members = .OK (0, .Full) := by decide
theorem off_rem : fieldOffset prog.prog_comp_env _payload_remain coEnc.co_members = .OK (8, .Full) := by decide
theorem off_xori : fieldOffset prog.prog_comp_env _xori coEnc.co_members = .OK (16, .Full) := by decide
theorem off_mask : fieldOffset prog.prog_comp_env _mask coEnc.co_members = .OK (20, .Full) := by decide
theorem off_fb : fieldOffset prog.prog_comp_env _firstbyte coEnc.co_members = .OK (24, .Full) := by decide
theorem off_cf : fieldOffset prog.prog_comp_env _contfragment coEnc.co_members
    = .OK (24, .Bits .I32 .Unsigned 8 1) := by decide

abbrev encT : Ty := Ty.Tstruct _ws_encoder noattr

/-- `enc->fld`（`enc` は一時変数で、ブロック `b` の先頭を指す）。 -/
theorem lv_enc {ge : CGenv} {E : Env} {le : TempEnv} {m : Mem} {b : Block} {fld : Ident} {ty : Ty}
    {delta : Z} {bf : Bitfield}
    (hcenv : ge.genv_cenv = prog.prog_comp_env) (hle : le.get _enc = some (.Vptr b Integers.Ptrofs.zero))
    (hoff : fieldOffset prog.prog_comp_env fld coEnc.co_members = .OK (delta, bf)) :
    EvalLvalue ge E le m (.Efield (.Ederef (.Etempvar _enc (tptr encT)) encT) fld ty) b
      (Integers.Ptrofs.add Integers.Ptrofs.zero (Integers.Ptrofs.repr delta)) bf :=
  EvalLvalue.Efield_struct _ _ _ b _ _ coEnc noattr delta bf
    (EvalExpr.Elvalue _ b _ .Full _ (EvalLvalue.Ederef _ _ b _ (EvalExpr.Etempvar _ _ _ hle))
      (DerefLoc.copy rfl))
    rfl (hcenv ▸ co_enc) (hcenv ▸ hoff)

end Deb2025_10148C
