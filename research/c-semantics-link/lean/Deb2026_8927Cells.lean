/-
担当 B（CVE-2026-8927・7168・3784）で共通に使う道具。生成された構文木には依存しない。

- 所有するメモリを「セルの並び」（`Cells`）で表す。読み出し（`cells_load`）、ポインタの有効性（`cells_weakValid`）、
  1つのセルの書き換え（`assign_cell`・`assign_bits_cell`）を、並びの中の位置で扱う
- 式の評価のうち、この3件で繰り返し出る形（`p->f`・`p->f1.f2`・`p->f1.f2[k]`・`*p`・ビットフィールド）
- 外部関数の弱い仕様（`retSpec`: 任意の引数で、決まった値を返し、メモリを変えない）
-/
import CCLib
import Case5Common
import Case4Common
import Case2Common
open CC CC.Sep CC.HProp
open Case5C (addr call_fwd RR return_const skip_end sep_l sep_r)
open Case4C (IsPtr loadResult_ptr cast_ptr mapsto_weakValid)

set_option maxRecDepth 20000

namespace Deb2026_8927

/-- 並びの `i` 番目の要素は並びに属する（`h` は具体的な並びの上で `rfl`）。 -/
theorem mem_idx {α : Type} : ∀ {cs : List α} {x : α} (i : Nat), cs[i]? = some x → x ∈ cs
  | [], _, _, h => by simp at h
  | y :: ys, x, 0, h => by simp at h; subst h; exact List.Mem.head _
  | y :: ys, x, i + 1, h => List.Mem.tail _ (mem_idx (cs := ys) i (by simpa using h))

/-! ## セルの並び -/

structure Cell where
  chunk : Chunk
  b : Block
  o : Z
  v : Val

def cellP (pm : Permission) (c : Cell) : HProp := mapsto c.chunk pm c.b c.o c.v

def Cells (pm : Permission) (cs : List Cell) : HProp := sepList (cs.map (cellP pm))

theorem cells_load {pm : Permission} {cs : List Cell} {hp : Heap} {m : Mem} {c : Cell}
    (hpr : permOrder pm .Readable = true) (hH : Cells pm cs hp) (hag : Heap.Agrees hp m)
    (hmem : c ∈ cs) : Mem.load c.chunk m c.b c.o = some (Val.loadResult c.chunk c.v) := by
  induction cs generalizing hp with
  | nil => cases hmem
  | cons x xs ih =>
    simp only [Cells, List.map, sepList] at hH
    rcases List.mem_cons.mp hmem with h | h
    · subst h
      obtain ⟨h1, c1, a1⟩ := sep_l hH hag
      exact mapsto_load hpr c1 a1
    · obtain ⟨h2, c2, a2⟩ := sep_r hH hag
      exact ih c2 a2 h

theorem cells_weakValid {pm : Permission} {cs : List Cell} {hp : Heap} {m : Mem} {c : Cell}
    (hpn : permOrder pm .Nonempty = true) (hH : Cells pm cs hp) (hag : Heap.Agrees hp m)
    (hmem : c ∈ cs) (hsz : 0 < sizeChunkNat c.chunk) :
    Mem.weakValidPointer m c.b c.o = true := by
  induction cs generalizing hp with
  | nil => cases hmem
  | cons x xs ih =>
    simp only [Cells, List.map, sepList] at hH
    rcases List.mem_cons.mp hmem with h | h
    · subst h
      obtain ⟨h1, c1, a1⟩ := sep_l hH hag
      exact mapsto_weakValid hpn c1 a1 hsz
    · obtain ⟨h2, c2, a2⟩ := sep_r hH hag
      exact ih c2 a2 h

theorem cells_middle (pm : Permission) (pre post : List Cell) (c : Cell) :
    Cells pm (pre ++ c :: post) = (cellP pm c ∗ Cells pm (pre ++ post)) := by
  unfold Cells
  rw [show (cellP pm c ∗ sepList ((pre ++ post).map (cellP pm)))
        = sepList ((c :: (pre ++ post)).map (cellP pm)) from rfl]
  exact sepList_perm (by simpa [List.map_append] using
    (List.perm_middle (a := cellP pm c) (l₁ := pre.map (cellP pm)) (l₂ := post.map (cellP pm))))

/-! ## 書き込み -/

/-- `a1 = a2;`（`a1` は並びの中のセル `x` を指す、ビットフィールドでない左辺値）。 -/
theorem assign_cell (ge fe f) (E : Env) (l : List (Ident × Val)) (pm : Permission)
    (pre post : List Cell) (x : Cell) (a1 a2 : Expr) (ofs : Integers.Ptrofs) (vnew : Val)
    (hpw : permOrder pm .Writable = true)
    (hacc : accessMode (typeof a1) = .By_value x.chunk)
    (hofs : x.o = Integers.Ptrofs.unsigned ofs)
    (hlv : ∀ le m hp, TempsHold l le → Cells pm (pre ++ x :: post) hp → Heap.Agrees hp m →
        EvalLvalue ge E le m a1 x.b ofs .Full)
    (hrv : ∀ le m hp, TempsHold l le → Cells pm (pre ++ x :: post) hp → Heap.Agrees hp m →
        ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some vnew) :
    Triple ge fe f (LocalSt E l (Cells pm (pre ++ x :: post))) (.Sassign a1 a2)
      (.only (LocalSt E l (Cells pm (pre ++ { x with v := vnew } :: post)))) := by
  refine triple_assign ge fe f _ _ a1 a2 x.chunk pm x.b ofs hpw hacc
    (fun e le hp m hP hag => ?_)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  have hH' := hH
  rw [cells_middle] at hH'
  obtain ⟨h1, h2, hd, rfl, hx, hrest⟩ := hH'
  refine ⟨x.v, vnew, h1, h2, hd, rfl, ?_, hlv le m _ hT hH hag, hrv le m _ hT hH hag, ?_⟩
  · rw [← hofs]; exact hx
  · intro h1' hm' hd'
    refine ⟨rfl, hT, ?_⟩
    rw [cells_middle]
    refine ⟨h1', h2, hd', rfl, ?_, hrest⟩
    show mapsto x.chunk pm x.b x.o vnew h1'
    rw [hofs]; exact hm'

/-- `a1 = a2;`（`a1` は `unsigned int f:1` のビットフィールド。セル `x` はそれを含む 32 bit の単位）。 -/
theorem assign_bits_cell (ge fe f) (E : Env) (l : List (Ident × Val)) (pm : Permission)
    (pre post : List Cell) (x : Cell) (w : Integers.Int) (a1 a2 : Expr) (ofs : Integers.Ptrofs)
    (pos : Z) (n : Integers.Int)
    (hpw : permOrder pm .Writable = true) (hpr : permOrder pm .Readable = true)
    (hty : typeof a1 = tint) (hpos0 : 0 ≤ pos) (hpos : pos + 1 ≤ 32)
    (hx : x.chunk = .Mint32 ∧ x.v = .Vint w)
    (hofs : x.o = Integers.Ptrofs.unsigned ofs)
    (hlv : ∀ le m hp, TempsHold l le → Cells pm (pre ++ x :: post) hp → Heap.Agrees hp m →
        EvalLvalue ge E le m a1 x.b ofs (.Bits .I32 .Unsigned pos 1))
    (hrv : ∀ le m hp, TempsHold l le → Cells pm (pre ++ x :: post) hp → Heap.Agrees hp m →
        ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some (.Vint n)) :
    Triple ge fe f (LocalSt E l (Cells pm (pre ++ x :: post))) (.Sassign a1 a2)
      (.only (LocalSt E l (Cells pm (pre ++
        { x with v := .Vint (Integers.Int.bitfield_insert (Cop.firstBit .I32 pos 1).toNat 1 w n) }
          :: post)))) := by
  obtain ⟨hch, hv⟩ := hx
  refine Case2C.triple_assign_bitfield ge fe f _ _ a1 a2 pm x.b ofs pos hpw hpr hty hpos0 hpos
    (fun e le hp m hP hag => ?_)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  have hH' := hH
  rw [cells_middle] at hH'
  obtain ⟨h1, h2, hd, rfl, hx1, hrest⟩ := hH'
  refine ⟨w, n, h1, h2, hd, rfl, ?_, hlv le m _ hT hH hag, hrv le m _ hT hH hag, ?_⟩
  · have : mapsto x.chunk pm x.b x.o x.v h1 := hx1
    rw [hch, hv, hofs] at this; exact this
  · intro h1' hm' hd'
    refine ⟨rfl, hT, ?_⟩
    rw [cells_middle]
    refine ⟨h1', h2, hd', rfl, ?_, hrest⟩
    show mapsto x.chunk pm x.b x.o _ h1'
    rw [hch, hofs]; exact hm'

/-! ## 式の評価 -/

theorem eval_deref_temp {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {p sid : Ident}
    {b : Block} {o : Integers.Ptrofs} (hle : le.get p = some (.Vptr b o)) :
    EvalExpr ge e le m (.Ederef (.Etempvar p (tptr (.Tstruct sid noattr))) (.Tstruct sid noattr))
      (.Vptr b o) :=
  EvalExpr.Elvalue _ b o .Full _ (EvalLvalue.Ederef _ _ b o (EvalExpr.Etempvar p _ _ hle))
    (DerefLoc.copy rfl)

/-- `p->fld` の左辺値。 -/
theorem lv_f1 {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {p sid fld : Ident} {ty : Ty}
    {co : Composite} {b : Block} {o : Integers.Ptrofs} {d : Z} {bf : Bitfield}
    (hle : le.get p = some (.Vptr b o)) (hco : ge.genv_cenv.get sid = some co)
    (hfld : fieldOffset ge.genv_cenv fld co.co_members = .OK (d, bf)) :
    EvalLvalue ge e le m
      (.Efield (.Ederef (.Etempvar p (tptr (.Tstruct sid noattr))) (.Tstruct sid noattr)) fld ty)
      b (Integers.Ptrofs.add o (Integers.Ptrofs.repr d)) bf :=
  EvalLvalue.Efield_struct _ fld ty b o sid co noattr d bf (eval_deref_temp hle) rfl hco hfld

/-- `p->f1.f2` の左辺値（`f1` は構造体）。 -/
theorem lv_f2 {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {p sid sid1 f1 f2 : Ident} {ty : Ty}
    {co co1 : Composite} {b : Block} {o : Integers.Ptrofs} {d1 d2 : Z} {bf : Bitfield}
    (hle : le.get p = some (.Vptr b o)) (hco : ge.genv_cenv.get sid = some co)
    (hf1 : fieldOffset ge.genv_cenv f1 co.co_members = .OK (d1, .Full))
    (hco1 : ge.genv_cenv.get sid1 = some co1)
    (hf2 : fieldOffset ge.genv_cenv f2 co1.co_members = .OK (d2, bf)) :
    EvalLvalue ge e le m
      (.Efield (.Efield (.Ederef (.Etempvar p (tptr (.Tstruct sid noattr))) (.Tstruct sid noattr)) f1
        (.Tstruct sid1 noattr)) f2 ty)
      b (Integers.Ptrofs.add (Integers.Ptrofs.add o (Integers.Ptrofs.repr d1)) (Integers.Ptrofs.repr d2))
      bf :=
  EvalLvalue.Efield_struct _ f2 ty b _ sid1 co1 noattr d2 bf
    (EvalExpr.Elvalue _ _ _ .Full _ (lv_f1 hle hco hf1) (DerefLoc.copy rfl)) rfl hco1 hf2

/-- 左辺値から値を読む（スカラー）。 -/
theorem eval_lv_load {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {a : Expr} {b : Block}
    {ofs : Integers.Ptrofs} {chunk : Chunk} {v : Val}
    (hlv : EvalLvalue ge e le m a b ofs .Full) (hacc : accessMode (typeof a) = .By_value chunk)
    (hload : Mem.load chunk m b (Integers.Ptrofs.unsigned ofs) = some v) :
    EvalExpr ge e le m a v :=
  EvalExpr.Elvalue _ b ofs .Full v hlv (DerefLoc.value chunk v hacc hload)

/-- 左辺値から値を読む（`unsigned int f:1` のビットフィールド）。 -/
theorem eval_lv_bit {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {a0 : Expr} {fld : Ident}
    {b : Block} {ofs : Integers.Ptrofs} {pos : Z} {w : Integers.Int}
    (hlv : EvalLvalue ge e le m (.Efield a0 fld tint) b ofs (.Bits .I32 .Unsigned pos 1))
    (hpos0 : 0 ≤ pos) (hpos : pos + 1 ≤ 32)
    (hload : Mem.load .Mint32 m b (Integers.Ptrofs.unsigned ofs) = some (.Vint w)) :
    EvalExpr ge e le m (.Efield a0 fld tint) (.Vint (Cop.bitfieldExtract .I32 .Unsigned pos 1 w)) :=
  EvalExpr.Elvalue _ b ofs (.Bits .I32 .Unsigned pos 1) _ hlv
    (DerefLoc.bitfield .I32 .Unsigned pos 1 _
      (Cop.LoadBitfield.intro .I32 .Signed noattr .Unsigned pos 1 m _ w hpos0
        (by decide) (by decide) hpos (by decide) hload))

/-- `*p`（`p` は一時変数）。 -/
theorem eval_deref_scalar {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {p : Ident} {ty : Ty}
    {chunk : Chunk} {b : Block} {o : Integers.Ptrofs} {v : Val}
    (hle : le.get p = some (.Vptr b o)) (hacc : accessMode ty = .By_value chunk)
    (hload : Mem.load chunk m b (Integers.Ptrofs.unsigned o) = some v) :
    EvalExpr ge e le m (.Ederef (.Etempvar p (tptr ty)) ty) v :=
  EvalExpr.Elvalue _ b o .Full v (EvalLvalue.Ederef _ _ b o (EvalExpr.Etempvar p _ _ hle))
    (DerefLoc.value chunk v hacc hload)

/-- `p->f1.f2[k]`（`f2` は `char *` の配列）の左辺値。 -/
theorem lv_arr {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {p sid sid1 f1 f2 : Ident}
    {co co1 : Composite} {b : Block} {o : Integers.Ptrofs} {d1 d2 : Z} {n : Z} {k : Integers.Int}
    (hle : le.get p = some (.Vptr b o)) (hco : ge.genv_cenv.get sid = some co)
    (hf1 : fieldOffset ge.genv_cenv f1 co.co_members = .OK (d1, .Full))
    (hco1 : ge.genv_cenv.get sid1 = some co1)
    (hf2 : fieldOffset ge.genv_cenv f2 co1.co_members = .OK (d2, .Full))
    (hcls : Cop.classifyAdd (tarray (tptr tschar) n) tint = .pi (tptr tschar) .Signed) :
    EvalLvalue ge e le m
      (.Ederef
        (.Ebinop .Oadd
          (.Efield (.Efield (.Ederef (.Etempvar p (tptr (.Tstruct sid noattr))) (.Tstruct sid noattr))
              f1 (.Tstruct sid1 noattr)) f2 (tarray (tptr tschar) n))
          (.Econst_int k tint) (tptr (tptr tschar))) (tptr tschar))
      b (Integers.Ptrofs.add
          (Integers.Ptrofs.add (Integers.Ptrofs.add o (Integers.Ptrofs.repr d1)) (Integers.Ptrofs.repr d2))
          (Integers.Ptrofs.mul (Integers.Ptrofs.repr (sizeof ge.genv_cenv (tptr tschar)))
            (Cop.ptrofsOfInt .Signed k))) .Full :=
  EvalLvalue.Ederef _ _ _ _
    (EvalExpr.Ebinop _ _ _ _ _ _ _
      (EvalExpr.Elvalue _ _ _ .Full _ (lv_f2 hle hco hf1 hco1 hf2) (DerefLoc.reference rfl))
      (EvalExpr.Econst_int _ _)
      (semAdd_ptr_int _ _ _ _ _ hcls))

/-! ## 真偽値 -/

theorem boolVal_vptr {b : Block} {o : Integers.Ptrofs} {t : Ty} {m : Mem}
    (hv : Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) :
    Cop.boolVal (.Vptr b o) (tptr t) m = some true := by
  unfold Cop.boolVal
  simp [Cop.classifyBool, typeconv, tptr, removeAttributes, tattr, hv, Archi.ptr64]

theorem boolVal_null {t : Ty} {m : Mem} :
    Cop.boolVal (.Vlong (Integers.Int64.repr 0)) (tptr t) m = some false := rfl

theorem notbool_vptr {b : Block} {o : Integers.Ptrofs} {t : Ty} {m : Mem}
    (hv : Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) :
    Cop.semUnaryOperation .Onotbool (.Vptr b o) (tptr t) m = some (Val.ofBool false) := by
  simp only [Cop.semUnaryOperation, Cop.semNotbool, boolVal_vptr hv]
  rfl

theorem notbool_null {t : Ty} {m : Mem} :
    Cop.semUnaryOperation .Onotbool (.Vlong (Integers.Int64.repr 0)) (tptr t) m
      = some (Val.ofBool true) := rfl

theorem boolVal_ofBool (b : Bool) (t : Ty) (m : Mem) (ht : t = tint ∨ t = tbool) :
    Cop.boolVal (Val.ofBool b) t m = some b := by
  rcases ht with rfl | rfl <;> cases b <;> rfl


/-! ## 文の規則 -/

/-- `do { body } while(0)`（`Sloop body Sbreak`）。本体を1回だけ通る。 -/
theorem triple_once (ge fe f) (P Q : Sep.Assn) (body : Stmt)
    (h : Triple ge fe f P body (.only Q)) :
    Triple ge fe f P (.Sloop body .Sbreak) (.only Q) :=
  triple_loop ge fe f (.only Q) (fun _ => P) (fun _ => Q) body .Sbreak
    (fun _ => triple_conseq ge fe f h (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x))
    (fun _ => triple_conseq ge fe f (triple_break ge fe f Q) (fun _ _ _ x => x)
      (fun _ _ _ x => False.elim x) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ x => x))
    0

/-- 並びの中のセルから読む（番地は左辺値の評価が出す形で与える）。 -/
theorem ld {pm : Permission} {cs : List Cell} {hp : Heap} {m : Mem} {x : Cell}
    {ofs : Integers.Ptrofs} (hpr : permOrder pm .Readable = true) (hH : Cells pm cs hp)
    (hag : Heap.Agrees hp m) (hmem : x ∈ cs) (hofs : x.o = Integers.Ptrofs.unsigned ofs) :
    Mem.load x.chunk m x.b (Integers.Ptrofs.unsigned ofs) = some (Val.loadResult x.chunk x.v) := by
  rw [← hofs]; exact cells_load hpr hH hag hmem

/-- 書き込みの規則を、並びの等式で包んだもの（`cs`・`cs'` は名前の付いた並びのまま渡せる）。 -/
theorem assign_at (ge fe f) (E : Env) (l : List (Ident × Val)) (pm : Permission)
    (cs cs' pre post : List Cell) (x : Cell) (a1 a2 : Expr) (ofs : Integers.Ptrofs) (vnew : Val)
    (hcs : cs = pre ++ x :: post) (hcs' : cs' = pre ++ { x with v := vnew } :: post)
    (hpw : permOrder pm .Writable = true)
    (hacc : accessMode (typeof a1) = .By_value x.chunk)
    (hofs : x.o = Integers.Ptrofs.unsigned ofs)
    (hlv : ∀ le m hp, TempsHold l le → Cells pm cs hp → Heap.Agrees hp m →
        EvalLvalue ge E le m a1 x.b ofs .Full)
    (hrv : ∀ le m hp, TempsHold l le → Cells pm cs hp → Heap.Agrees hp m →
        ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some vnew) :
    Triple ge fe f (LocalSt E l (Cells pm cs)) (.Sassign a1 a2)
      (.only (LocalSt E l (Cells pm cs'))) := by
  subst hcs hcs'
  exact assign_cell ge fe f E l pm pre post x a1 a2 ofs vnew hpw hacc hofs hlv hrv

theorem assign_bits_at (ge fe f) (E : Env) (l : List (Ident × Val)) (pm : Permission)
    (cs cs' pre post : List Cell) (x : Cell) (w : Integers.Int) (a1 a2 : Expr)
    (ofs : Integers.Ptrofs) (pos : Z) (n : Integers.Int)
    (hcs : cs = pre ++ x :: post)
    (hcs' : cs' = pre ++
      { x with v := .Vint (Integers.Int.bitfield_insert (Cop.firstBit .I32 pos 1).toNat 1 w n) }
        :: post)
    (hpw : permOrder pm .Writable = true) (hpr : permOrder pm .Readable = true)
    (hty : typeof a1 = tint) (hpos0 : 0 ≤ pos) (hpos : pos + 1 ≤ 32)
    (hx : x.chunk = .Mint32 ∧ x.v = .Vint w)
    (hofs : x.o = Integers.Ptrofs.unsigned ofs)
    (hlv : ∀ le m hp, TempsHold l le → Cells pm cs hp → Heap.Agrees hp m →
        EvalLvalue ge E le m a1 x.b ofs (.Bits .I32 .Unsigned pos 1))
    (hrv : ∀ le m hp, TempsHold l le → Cells pm cs hp → Heap.Agrees hp m →
        ∃ v2, EvalExpr ge E le m a2 v2 ∧ Cop.semCast v2 (typeof a2) (typeof a1) m = some (.Vint n)) :
    Triple ge fe f (LocalSt E l (Cells pm cs)) (.Sassign a1 a2)
      (.only (LocalSt E l (Cells pm cs'))) := by
  subst hcs hcs'
  exact assign_bits_cell ge fe f E l pm pre post x w a1 a2 ofs pos n hpw hpr hty hpos0 hpos hx hofs
    hlv hrv

/-- 前提の書き換え（`LocalSt` の所有の部分を、等しい形に置き換える）。 -/
theorem triple_cells_eq (ge fe f) (E : Env) (l : List (Ident × Val)) (A B : HProp) (s : Stmt)
    (R : Sep.ExitConds) (hAB : A = B) (h : Triple ge fe f (LocalSt E l B) s R) :
    Triple ge fe f (LocalSt E l A) s R := by
  subst hAB; exact h

/-- 追う一時変数の並びを減らす（前提の側）。 -/
theorem triple_pre_sub (ge fe f) (E : Env) (l l0 : List (Ident × Val)) (H : HProp) (s : Stmt)
    (R : Sep.ExitConds) (hsub : ∀ p ∈ l0, p ∈ l) (h : Triple ge fe f (LocalSt E l0 H) s R) :
    Triple ge fe f (LocalSt E l H) s R :=
  triple_pre ge fe f (fun _ _ _ ⟨he, hT, hH⟩ => ⟨he, fun p hp => hT p (hsub p hp), hH⟩) h

/-- 追う一時変数の並びを減らす（事後の側）。 -/
theorem triple_post_sub (ge fe f) (P : Sep.Assn) (E : Env) (l l' : List (Ident × Val)) (H : HProp)
    (s : Stmt) (hsub : ∀ p ∈ l, p ∈ l') (h : Triple ge fe f P s (.only (LocalSt E l' H))) :
    Triple ge fe f P s (.only (LocalSt E l H)) :=
  triple_conseq ge fe f h (fun _ _ _ x => x)
    (fun _ _ _ ⟨he, hT, hH⟩ => ⟨he, fun p hp => hT p (hsub p hp), hH⟩)
    (fun _ _ _ x => False.elim x) (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x)

/-- `break; …`（`switch` の `default: break;`）。後ろの文には到達しない。 -/
theorem break_seq (ge fe f) (P : Sep.Assn) (s : Stmt) (R : Sep.ExitConds)
    (hb : ∀ e le hp, P e le hp → R.brk e le hp) :
    Triple ge fe f P (.Ssequence .Sbreak s) R :=
  triple_seq ge fe f P Sep.Assn.no R .Sbreak s
    (triple_conseq ge fe f (triple_break ge fe f P) (fun _ _ _ x => x)
      (fun _ _ _ x => False.elim x) hb (fun _ _ _ x => False.elim x) (fun _ _ x => False.elim x))
    (triple_vacuous ge fe f _ _)

theorem notbool_long {x : Integers.Int64} {m : Mem} :
    Cop.semUnaryOperation .Onotbool (.Vlong x) tlong m
      = some (Val.ofBool (Integers.Int64.eq x Integers.Int64.zero)) := by
  have h : Cop.semUnaryOperation .Onotbool (.Vlong x) tlong m
      = some (Val.ofBool (!!(Integers.Int64.eq x Integers.Int64.zero))) := rfl
  rw [h, Bool.not_not]

/-! ## 外部関数の弱い仕様 -/

/-- 任意の引数で呼ばれ、`r` を返し、メモリを変えない。 -/
def retSpec (tyargs : List Ty) (tyres : Ty) (r : Val) : FunSpec where
  tyargs := tyargs
  tyres := tyres
  cc := cc_default
  pre := fun _ hp => emp hp
  post := fun v hp => v = r ∧ emp hp
  measure := fun _ => 0

/-- `retSpec` の関数を呼び、戻り値を一時変数に入れる。 -/
theorem call_ret (ge fe f) (tyargs : List Ty) (tyres : Ty) (r : Val) (id : Ident) (callee : Expr)
    (al : List Expr) (E : Env) (l : List (Ident × Val)) (Hk : HProp) (vargs : List Val)
    (fb : Block) (fd : FunDef)
    (hspec : ∀ vs, SatisfiesAt ge fe fd (retSpec tyargs tyres r) vs)
    (hfind : FuncPtr ge fb fd)
    (hty : typeOfFundef fd = .Tfunction tyargs tyres cc_default)
    (hclass : Cop.classifyFun (typeof callee) = .f tyargs tyres cc_default)
    (hcallee : ∀ le m, TempsHold l le → EvalExpr ge E le m callee (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge E le m al tyargs vargs) :
    Triple ge fe f (LocalSt E l Hk) (.Scall (some id) callee al)
      (.only (LocalSt E (setLocal l id r) Hk)) :=
  call_fwd ge fe f (retSpec tyargs tyres r) id callee al E l emp Hk emp Hk Hk vargs r fb fd
    hspec hfind hty hclass hcallee hargs (fun _ h => h) (fun _ _ h => h) (emp_sep_eq _).symm (emp_sep_eq _)

/-- 戻り値の無い呼び出しで、仕様が所有の全体を書き換える（`A` から `B` へ）。 -/
theorem call_void_cells (ge fe f) (S : FunSpec) (callee : Expr) (al : List Expr)
    (E : Env) (l : List (Ident × Val)) (A B : HProp) (vargs : List Val) (fb : Block) (fd : FunDef)
    (hspec : ∀ vs, SatisfiesAt ge fe fd S vs)
    (hfind : FuncPtr ge fb fd)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun (typeof callee) = .f S.tyargs S.tyres S.cc)
    (hcallee : ∀ le m, TempsHold l le → EvalExpr ge E le m callee (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge E le m al S.tyargs vargs)
    (hpre : ∀ h, A h → S.pre vargs h)
    (hpost : ∀ v h, S.post v h → B h) :
    Triple ge fe f (LocalSt E l A) (.Scall none callee al) (.only (LocalSt E l B)) := by
  refine triple_call ge fe f S none callee al _ _ fb fd hspec hfind hty hclass
    (fun e le hp m hP hag => ?_)
  obtain ⟨he, hT, hH⟩ := hP
  subst he
  refine ⟨vargs, hp, Heap.emp, ?_, (Heap.union_emp hp).symm,
    hcallee le m hT, hargs le m hT, hpre _ hH, ?_⟩
  · exact Heap.disjoint_comm (Heap.disjoint_emp_left hp)
  intro v h1' hS _
  exact ⟨rfl, hT, by rw [Heap.union_emp]; exact hpost v h1' hS⟩

/-- 戻り値を一時変数に入れる呼び出しで、仕様が所有の全体を書き換える。 -/
theorem call_set_cells (ge fe f) (S : FunSpec) (id : Ident) (callee : Expr) (al : List Expr)
    (E : Env) (l : List (Ident × Val)) (A B : HProp) (vargs : List Val) (vret : Val)
    (fb : Block) (fd : FunDef)
    (hspec : ∀ vs, SatisfiesAt ge fe fd S vs)
    (hfind : FuncPtr ge fb fd)
    (hty : typeOfFundef fd = .Tfunction S.tyargs S.tyres S.cc)
    (hclass : Cop.classifyFun (typeof callee) = .f S.tyargs S.tyres S.cc)
    (hcallee : ∀ le m, TempsHold l le → EvalExpr ge E le m callee (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge E le m al S.tyargs vargs)
    (hpre : ∀ h, A h → S.pre vargs h)
    (hpost : ∀ v h, S.post v h → v = vret ∧ B h) :
    Triple ge fe f (LocalSt E l A) (.Scall (some id) callee al)
      (.only (LocalSt E (setLocal l id vret) B)) :=
  call_fwd ge fe f S id callee al E l A emp B A B vargs vret fb fd hspec hfind hty hclass hcallee
    hargs hpre hpost (sep_emp_eq _).symm (sep_emp_eq _)

end Deb2026_8927
