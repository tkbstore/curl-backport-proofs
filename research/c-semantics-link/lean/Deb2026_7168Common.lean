/-
CVE-2026-7168: 上流（U）と 8.14.1（D）で共通に使う、所有するメモリの形。生成された構文木には依存しない。
レイアウトの違い（`str` の位置、`state` の位置、`authproxy.picked` の型）は `Lay` で与える。
-/
import Deb2026_7168Locals
import Deb2026_8927U1
open CC CC.Sep CC.HProp
open Deb2026_8927

set_option maxRecDepth 20000

namespace Deb2026_7168

/-- 読み書きするメモリの置き場所と、変わらない値。 -/
structure Ctx where
  dataB : Block
  dataO : Integers.Ptrofs
  oldB : Block              -- data->set.str[STRING_PROXY] の元の値（NULL でない）
  oldO : Integers.Ptrofs
  old0 : Integers.Int       -- その先頭の1バイト（ポインタが有効であることを言うためだけに所有する）
  pB : Block                -- 新しいプロキシ文字列 ptr（NULL でない）
  pO : Integers.Ptrofs
  p0 : Integers.Int
  nonce0 : Val              -- data->state.proxydigest.nonce の元の値
  picked0 : Val             -- data->state.authproxy.picked の元の値

/-- 関数の実行で変わる値。 -/
structure St where
  str : Val                 -- data->set.str[STRING_PROXY]
  nonce : Val
  picked : Val

/-- 版ごとのレイアウト。 -/
structure Lay where
  strBase : Z               -- struct UserDefined の中の str の位置
  stateOff : Z              -- struct Curl_easy の中の state の位置
  pch : Chunk               -- authproxy.picked の型（上流は uint32_t、8.14.1 は unsigned long）
  pzero : Val               -- その 0

/-- 上流: str は 8、state は 456、picked は uint32_t。 -/
def layU : Lay := ⟨8, 456, .Mint32, .Vint (Integers.Int.repr 0)⟩
/-- 8.14.1: str は 128、state は 616、picked は unsigned long。 -/
def layD : Lay := ⟨128, 616, .Mint64, .Vlong (Integers.Int64.repr 0)⟩

/-- `data->set.str[STRING_PROXY]`（添字 32）の番地。 -/
def strP (L : Lay) (o : Integers.Ptrofs) : Integers.Ptrofs :=
  Integers.Ptrofs.add (f2 o 0 L.strBase)
    (Integers.Ptrofs.mul (Integers.Ptrofs.repr 8) (Cop.ptrofsOfInt .Signed (Integers.Int.repr 32)))

def cStr (L : Lay) (c : Ctx) (s : St) : Deb2026_8927.Cell := ⟨Mptr, c.dataB, u (strP L c.dataO), s.str⟩
def cNonce (L : Lay) (c : Ctx) (s : St) : Deb2026_8927.Cell := ⟨Mptr, c.dataB, u (f1 (f2 c.dataO L.stateOff 0) 0), s.nonce⟩
def cPicked (L : Lay) (c : Ctx) (s : St) : Deb2026_8927.Cell :=
  ⟨L.pch, c.dataB, u (f1 (f2 c.dataO L.stateOff 8) 0), s.picked⟩
def cOld (c : Ctx) : Deb2026_8927.Cell := ⟨.Mint8signed, c.oldB, u c.oldO, .Vint c.old0⟩
def cPtr (c : Ctx) : Deb2026_8927.Cell := ⟨.Mint8signed, c.pB, u c.pO, .Vint c.p0⟩

abbrev cells (L : Lay) (c : Ctx) (s : St) : List Deb2026_8927.Cell :=
  [cStr L c s, cNonce L c s, cPicked L c s, cOld c, cPtr c]

def s0 (c : Ctx) : St := ⟨.Vptr c.oldB c.oldO, c.nonce0, c.picked0⟩

/-- プロキシが変わったとき（`strcmp` が 0 でない）の、戻った時点の値。 -/
def sChg (L : Lay) (sv : Val) : St := ⟨sv, vnull, L.pzero⟩

/-- 修正後の関数が戻った時点の値（`same` は `strcmp` が 0 を返したか）。 -/
def sAfter (L : Lay) (c : Ctx) (same : Bool) (sv : Val) : St := cond same (s0 c) (sChg L sv)

/-- 修正前の関数が戻った時点の値（`str` だけが変わる）。 -/
def sBefore (c : Ctx) (sv : Val) : St := ⟨sv, c.nonce0, c.picked0⟩

theorem envUP_none (iu ip : Ident) (b1 b2 : Block) (id : Ident) (h1 : id ≠ iu) (h2 : id ≠ ip) :
    (envUP iu ip b1 b2).get id = none := by
  unfold envUP
  rw [PTree.gso _ _ _ _ (Ne.symm h2), PTree.gso _ _ _ _ (Ne.symm h1)]
  exact PTree.gempty id

theorem notbool_int {r : Integers.Int} {m : Mem} :
    Cop.semUnaryOperation .Onotbool (.Vint r) tint m
      = some (Val.ofBool (Integers.Int.eq r Integers.Int.zero)) := by
  have h : Cop.semUnaryOperation .Onotbool (.Vint r) tint m
      = some (Val.ofBool (!!(Integers.Int.eq r Integers.Int.zero))) := rfl
  rw [h, Bool.not_not]

theorem cast_ofBool_int_bool (b : Bool) (m : Mem) :
    Cop.semCast (Val.ofBool b) tint tbool m = some (Val.ofBool b) := by cases b <;> rfl

end Deb2026_7168
