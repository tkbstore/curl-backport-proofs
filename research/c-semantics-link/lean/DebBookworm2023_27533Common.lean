/-
CVE-2023-27533 bookworm: 4つの翻訳単位に共通の部分。
性質は `research/backport-proof-debian/cases/bookworm/CVE-2023-27533.md`（証明の前にコミットした）。

前置き（`debbookworm2023_27533/prelude.h`）は4つで同じなので、構造体の環境も同じ形になる。
番地は、Clight の意味論が `Efield`・`Oadd` で計算するのと同じ式で書く（算術の補題を要らなくするため）。
-/
import GenDebBookworm2023_27533U1
import GenDebBookworm2023_27533U0
import GenDebBookworm2023_27533D1
import GenDebBookworm2023_27533D0
import Case3Common
open CC CC.Sep CC.HProp
open Case5C (addr call_fwd sep_l sep_r)
open Case4C (IsPtr cast_ptr mapsto_weakValid)

set_option maxRecDepth 20000

namespace DebBookworm2023_27533C

abbrev P := Integers.Ptrofs

/-! ## 番地 -/

/-- `str++`（`char *` に 1 を足す）の番地。 -/
def nextO (o : P) : P :=
  Integers.Ptrofs.add o
    (Integers.Ptrofs.mul (Integers.Ptrofs.repr 1) (Integers.Ptrofs.of_ints (Integers.Int.repr 1)))

/-- 文字列の先頭から `i` 文字目の番地。 -/
def offs (o : P) : Nat → P
  | 0 => o
  | i + 1 => nextO (offs o i)

def fld (o : P) (d : Z) : P := Integers.Ptrofs.add o (Integers.Ptrofs.repr d)

/-- `data->conn` -/
def oConn (o : P) : P := fld o 0
/-- `data->req.p.telnet` -/
def oTel (o : P) : P := fld (fld (fld o 8) 0) 0
/-- `data->state.aptr.user` -/
def oAu (o : P) : P := fld (fld (fld o 16) 0) 0
/-- `data->set.telnet_options` -/
def oOpt (o : P) : P := fld (fld o 24) 0
/-- `tn->telnet_vars` -/
def oVars (o : P) : P := fld o 2216
/-- `tn->us_preferred[CURL_TELOPT_NEW_ENVIRON]`（39） -/
def oPref (o : P) : P :=
  Integers.Ptrofs.add (fld o 0)
    (Integers.Ptrofs.mul (Integers.Ptrofs.repr 4) (Integers.Ptrofs.of_ints (Integers.Int.repr 39)))

/-! ## 文字列 -/

/-- `byte` の `i` 文字目から `cnt` 文字を所有する。 -/
def strH (p : Permission) (b : Block) (o : P) (byte : Nat → Integers.Int) : Nat → Nat → HProp
  | _, 0 => emp
  | i, cnt + 1 => mapsto .Mint8signed p b (Integers.Ptrofs.unsigned (offs o i)) (.Vint (byte i))
      ∗ strH p b o byte (i + 1) cnt

theorem strH_load {p : Permission} {b : Block} {o : P} {byte : Nat → Integers.Int}
    (hpr : permOrder p .Readable = true) :
    ∀ (cnt i k : Nat) (h : Heap) (m : Mem), k < cnt → strH p b o byte i cnt h → Heap.Agrees h m →
      Mem.load .Mint8signed m b (Integers.Ptrofs.unsigned (offs o (i + k)))
        = some (Val.loadResult .Mint8signed (.Vint (byte (i + k))))
  | 0, _, _, _, _, hk, _, _ => absurd hk (Nat.not_lt_zero _)
  | cnt + 1, i, 0, h, m, _, hs, hag => by
      obtain ⟨h1, c1, a1⟩ := sep_l hs hag
      exact mapsto_load hpr c1 a1
  | cnt + 1, i, k + 1, h, m, hk, hs, hag => by
      obtain ⟨h2, c2, a2⟩ := sep_r hs hag
      have := strH_load hpr cnt (i + 1) k h2 m (by omega) c2 a2
      rw [show i + (k + 1) = i + 1 + k by omega]
      exact this

/-- `*str & 0x80` が 0 でない（C の式のまま。`*str` は `char` を読んで符号拡張した値）。 -/
def hiBit (x : Integers.Int) : Bool :=
  !Integers.Int.eq (Integers.Int.and (Integers.Int.sign_ext 8 x) (Integers.Int.repr 128)) Integers.Int.zero

/-! ## 読む・書くメモリ -/

structure Ctx where
  dB : Block              -- data
  dO : P
  tnB : Block             -- data->req.p.telnet
  tnO : P
  cnB : Block             -- data->conn
  cnO : P
  auB : Block             -- data->state.aptr.user（NULL でない）
  auO : P
  au0 : Integers.Int      -- aptr.user[0]
  sB : Block              -- conn->user
  sO : P
  byte : Nat → Integers.Int   -- conn->user の各文字
  j : Nat                 -- 8 ビット目の立った文字の位置
  n : Nat                 -- strlen(conn->user)
  optV : Val              -- data->set.telnet_options
  varsV : Val             -- tn->telnet_vars
  pref : Integers.Int     -- tn->us_preferred[39]
  pm : Permission

/-- 呼び出しの前後で変わらない部分（`tn` の2つのセルを除く）。 -/
def K (c : Ctx) : HProp :=
  mapsto Mptr c.pm c.dB (Integers.Ptrofs.unsigned (oConn c.dO)) (.Vptr c.cnB c.cnO) ∗
  (mapsto Mptr c.pm c.dB (Integers.Ptrofs.unsigned (oTel c.dO)) (.Vptr c.tnB c.tnO) ∗
  (mapsto Mptr c.pm c.dB (Integers.Ptrofs.unsigned (oAu c.dO)) (.Vptr c.auB c.auO) ∗
  (mapsto Mptr c.pm c.dB (Integers.Ptrofs.unsigned (oOpt c.dO)) c.optV ∗
  (mapsto Mptr c.pm c.cnB (Integers.Ptrofs.unsigned (fld c.cnO 0)) (.Vptr c.sB c.sO) ∗
  (mapsto .Mint8signed c.pm c.auB (Integers.Ptrofs.unsigned c.auO) (.Vint c.au0) ∗
   strH c.pm c.sB c.sO c.byte 0 (c.j + 1)))))))

/-- `tn` の2つのセル。 -/
def T (c : Ctx) (vars : Val) (pref : Integers.Int) : HProp :=
  mapsto Mptr c.pm c.tnB (Integers.Ptrofs.unsigned (oVars c.tnO)) vars ∗
  mapsto .Mint32 c.pm c.tnB (Integers.Ptrofs.unsigned (oPref c.tnO)) (.Vint pref)

def H (c : Ctx) : HProp := T c c.varsV c.pref ∗ K c

structure Loads (c : Ctx) (m : Mem) : Prop where
  conn : Mem.load Mptr m c.dB (Integers.Ptrofs.unsigned (oConn c.dO)) = some (.Vptr c.cnB c.cnO)
  tel : Mem.load Mptr m c.dB (Integers.Ptrofs.unsigned (oTel c.dO)) = some (.Vptr c.tnB c.tnO)
  au : Mem.load Mptr m c.dB (Integers.Ptrofs.unsigned (oAu c.dO)) = some (.Vptr c.auB c.auO)
  opt : Mem.load Mptr m c.dB (Integers.Ptrofs.unsigned (oOpt c.dO)) = some (Val.loadResult Mptr c.optV)
  user : Mem.load Mptr m c.cnB (Integers.Ptrofs.unsigned (fld c.cnO 0)) = some (.Vptr c.sB c.sO)
  auv : Mem.weakValidPointer m c.auB (Integers.Ptrofs.unsigned c.auO) = true
  byte : ∀ k, k ≤ c.j → Mem.load .Mint8signed m c.sB (Integers.Ptrofs.unsigned (offs c.sO k))
    = some (Val.loadResult .Mint8signed (.Vint (c.byte k)))

theorem K_loads {c : Ctx} {hp : Heap} {m : Mem} (hpr : permOrder c.pm .Readable = true)
    (hpn : permOrder c.pm .Nonempty = true)
    (hK : K c hp) (hag : Heap.Agrees hp m) : Loads c m := by
  obtain ⟨h1, c1, a1⟩ := sep_l hK hag
  obtain ⟨r1, d1, b1⟩ := sep_r hK hag
  obtain ⟨h2, c2, a2⟩ := sep_l d1 b1
  obtain ⟨r2, d2, b2⟩ := sep_r d1 b1
  obtain ⟨h3, c3, a3⟩ := sep_l d2 b2
  obtain ⟨r3, d3, b3⟩ := sep_r d2 b2
  obtain ⟨h4, c4, a4⟩ := sep_l d3 b3
  obtain ⟨r4, d4, b4⟩ := sep_r d3 b3
  obtain ⟨h5, c5, a5⟩ := sep_l d4 b4
  obtain ⟨r5, d5, b5⟩ := sep_r d4 b4
  obtain ⟨h6, c6, a6⟩ := sep_l d5 b5
  obtain ⟨h7, c7, a7⟩ := sep_r d5 b5
  refine ⟨mapsto_load hpr c1 a1, mapsto_load hpr c2 a2, mapsto_load hpr c3 a3,
    mapsto_load hpr c4 a4, mapsto_load hpr c5 a5, mapsto_weakValid hpn c6 a6 (by decide), ?_⟩
  intro k hk
  have := strH_load hpr (c.j + 1) 0 k h7 m (by omega) c7 a7
  simpa using this

theorem H_loads {c : Ctx} {vars : Val} {pref : Integers.Int} {hp : Heap} {m : Mem}
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hH : (T c vars pref ∗ K c) hp) (hag : Heap.Agrees hp m) : Loads c m := by
  obtain ⟨h2, c2, a2⟩ := sep_r hH hag
  exact K_loads hpr hpn c2 a2

/-! ## 式の値 -/

section
variable {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem}

/-- 構造体の値を持つ `Efield`（内側の構造体。値はその番地）。 -/
theorem ev_sfld {a : Expr} {f sid sid' : Ident} {co : Composite} {b : Block} {o : P} {delta : Z}
    (hptr : EvalExpr ge e le m a (.Vptr b o)) (hty : typeof a = .Tstruct sid noattr)
    (hco : ge.genv_cenv.get sid = some co)
    (hfld : fieldOffset ge.genv_cenv f co.co_members = .OK (delta, .Full)) :
    EvalExpr ge e le m (.Efield a f (.Tstruct sid' noattr)) (.Vptr b (fld o delta)) :=
  EvalExpr.Elvalue _ _ _ .Full _
    (EvalLvalue.Efield_struct a f _ b o sid co noattr delta .Full hptr hty hco hfld)
    (DerefLoc.copy rfl)

/-- スカラーの `Efield`。 -/
theorem ev_vfld {a : Expr} {f sid : Ident} {ty : Ty} {co : Composite} {chunk : Chunk}
    {b : Block} {o : P} {delta : Z} {v : Val}
    (hptr : EvalExpr ge e le m a (.Vptr b o)) (hty : typeof a = .Tstruct sid noattr)
    (hco : ge.genv_cenv.get sid = some co)
    (hfld : fieldOffset ge.genv_cenv f co.co_members = .OK (delta, .Full))
    (hacc : accessMode ty = .By_value chunk)
    (hload : Mem.load chunk m b (Integers.Ptrofs.unsigned (fld o delta)) = some v) :
    EvalExpr ge e le m (.Efield a f ty) v :=
  EvalExpr.Elvalue _ _ _ .Full _
    (EvalLvalue.Efield_struct a f ty b o sid co noattr delta .Full hptr hty hco hfld)
    (DerefLoc.value chunk v hacc hload)

theorem ev_deref {p sid : Ident} {b : Block} {o : P} (hle : le.get p = some (.Vptr b o)) :
    EvalExpr ge e le m (.Ederef (.Etempvar p (tptr (.Tstruct sid noattr))) (.Tstruct sid noattr))
      (.Vptr b o) :=
  Case4C.eval_deref_temp hle

end

/-! ## 呼ばれる側 -/

/-- `strlen(conn->user)` は `n` を返し、メモリを変えない。 -/
def strlenSpec (c : Ctx) : FunSpec where
  tyargs := [tptr tschar]
  tyres := tulong
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.sB c.sO] ∧ emp hp
  post := fun v hp => v = .Vlong (Integers.Int64.repr c.n) ∧ emp hp
  measure := fun _ => 0

structure StrlenExt (ge : CGenv) (c : Ctx) where
  b : Block
  fd : FunDef
  hs : Genv.findSymbol ge.genv_genv (identOfString "strlen") = some b
  hf : FuncPtr ge b fd
  hty : typeOfFundef fd = .Tfunction (strlenSpec c).tyargs (strlenSpec c).tyres (strlenSpec c).cc
  hsat : ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fd (strlenSpec c) vs

/-- `str_is_nonascii(conn->user)` の仕様: 真（1）を返し、メモリを変えない。本体から示す。 -/
def sinSpec (c : Ctx) (Hh : HProp) : FunSpec where
  tyargs := [tptr tschar]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.sB c.sO] ∧ Hh hp
  post := fun v hp => v = .Vint (Integers.Int.repr 1) ∧ Hh hp
  measure := fun _ => 0

end DebBookworm2023_27533C
