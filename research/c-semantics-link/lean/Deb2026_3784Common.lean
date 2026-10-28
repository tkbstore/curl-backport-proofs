/-
CVE-2026-3784: 4つの版で共通に使う、所有するメモリの形と補題。生成された構文木には依存しない。
-/
import Deb2026_7168Common
open CC CC.Sep CC.HProp
open Deb2026_8927 (Cells retSpec u f1 f2 ld)

set_option maxRecDepth 20000

namespace Deb2026_3784

/-- `proxy_info_matches(data, needle)` が読む2つの `struct proxy_info` の置き場所と中身。 -/
structure Ctx where
  dB : Block
  dO : Integers.Ptrofs
  nB : Block
  nO : Integers.Ptrofs
  ptD : Integers.Int        -- data->proxytype
  ptN : Integers.Int
  portD : Integers.Int      -- data->port
  portN : Integers.Int
  nameD : Val               -- data->host.name
  nameN : Val
  uD : Val                  -- data->user
  uN : Val
  pD : Val                  -- data->passwd
  pN : Val

/-- 版ごとのレイアウト（`port` の型と位置、`proxytype` の位置）。 -/
structure Lay where
  pch : Chunk
  poff : Z
  ptoff : Z

def cPtD (L : Lay) (c : Ctx) : Deb2026_8927.Cell := ⟨.Mint8unsigned, c.dB, u (f1 c.dO L.ptoff), .Vint c.ptD⟩
def cPtN (L : Lay) (c : Ctx) : Deb2026_8927.Cell := ⟨.Mint8unsigned, c.nB, u (f1 c.nO L.ptoff), .Vint c.ptN⟩
def cPortD (L : Lay) (c : Ctx) : Deb2026_8927.Cell := ⟨L.pch, c.dB, u (f1 c.dO L.poff), .Vint c.portD⟩
def cPortN (L : Lay) (c : Ctx) : Deb2026_8927.Cell := ⟨L.pch, c.nB, u (f1 c.nO L.poff), .Vint c.portN⟩
def cNameD (c : Ctx) : Deb2026_8927.Cell := ⟨Mptr, c.dB, u (f2 c.dO 0 0), c.nameD⟩
def cNameN (c : Ctx) : Deb2026_8927.Cell := ⟨Mptr, c.nB, u (f2 c.nO 0 0), c.nameN⟩
def cUD (c : Ctx) : Deb2026_8927.Cell := ⟨Mptr, c.dB, u (f1 c.dO 16), c.uD⟩
def cUN (c : Ctx) : Deb2026_8927.Cell := ⟨Mptr, c.nB, u (f1 c.nO 16), c.uN⟩
def cPD (c : Ctx) : Deb2026_8927.Cell := ⟨Mptr, c.dB, u (f1 c.dO 24), c.pD⟩
def cPN (c : Ctx) : Deb2026_8927.Cell := ⟨Mptr, c.nB, u (f1 c.nO 24), c.pN⟩

abbrev cells (L : Lay) (c : Ctx) : List Deb2026_8927.Cell :=
  [cPtD L c, cPtN L c, cPortD L c, cPortN L c, cNameD c, cNameN c, cUD c, cUN c, cPD c, cPN c]

theorem if_true_triple {ge : CGenv} {fe : EntryRel} {f : Function} {P : Sep.Assn} {R : Sep.ExitConds}
    {bb : Bool} {s1 s2 : Stmt} (h : bb = true) (x : Triple ge fe f P s1 R) :
    Triple ge fe f P (if bb then s1 else s2) R := by rw [h]; exact x

theorem if_false_triple {ge : CGenv} {fe : EntryRel} {f : Function} {P : Sep.Assn} {R : Sep.ExitConds}
    {bb : Bool} {s1 s2 : Stmt} (h : bb = false) (x : Triple ge fe f P s2 R) :
    Triple ge fe f P (if bb then s1 else s2) R := by rw [h]; exact x

theorem cast_int_bool (x : Integers.Int) (m : Mem) :
    Cop.semCast (.Vint x) tint tbool m = some (Val.ofBool (!Integers.Int.eq x Integers.Int.zero)) := by
  cases h : Integers.Int.eq x Integers.Int.zero <;>
    simp [Cop.semCast, Cop.classifyCast, h, Val.ofBool] <;> rfl

/-- 引数の対で決まる値を返す関数（`Curl_timestrcmp`）の、ある引数での呼び出し。 -/
def tsAt (v0 : List Val) (r : Integers.Int) : FunSpec :=
  { retSpec [tptr tschar, tptr tschar] tint (.Vint r) with pre := fun vs hp => vs = v0 ∧ emp hp }

theorem call_ret_at (ge : CGenv) (fe : EntryRel) (f : Function) (ts : List Val → Integers.Int) {fd : FunDef}
    (hTs : ∀ vs, SatisfiesAt ge fe fd (retSpec [tptr tschar, tptr tschar] tint (.Vint (ts vs))) vs)
    (id : Ident) (callee : Expr) (al : List Expr) (E : Env) (l : List (Ident × Val)) (Hk : HProp)
    (vargs : List Val) (fb : Block)
    (hfind : FuncPtr ge fb fd)
    (hty : typeOfFundef fd = .Tfunction [tptr tschar, tptr tschar] tint cc_default)
    (hclass : Cop.classifyFun (typeof callee) = .f [tptr tschar, tptr tschar] tint cc_default)
    (hcallee : ∀ le m, TempsHold l le → EvalExpr ge E le m callee (.Vptr fb Integers.Ptrofs.zero))
    (hargs : ∀ le m, TempsHold l le → EvalExprlist ge E le m al [tptr tschar, tptr tschar] vargs) :
    Triple ge fe f (LocalSt E l Hk) (.Scall (some id) callee al)
      (.only (LocalSt E (setLocal l id (.Vint (ts vargs))) Hk)) :=
  Case5C.call_fwd ge fe f (tsAt vargs (ts vargs)) id callee al E l emp Hk emp Hk Hk vargs (.Vint (ts vargs))
    fb fd (fun vs k m hp hf hk hpre hd hag => by
      obtain ⟨rfl, he⟩ := hpre
      exact hTs vs k m hp hf hk he hd hag)
    hfind hty hclass hcallee hargs (fun _ h => ⟨rfl, h⟩) (fun _ _ h => h) (emp_sep_eq _).symm (emp_sep_eq _)

set_option hygiene false in
macro "ldc3 " i:num x:term:max : term => `(ld hpr hH hag (x := $x) (Deb2026_8927.mem_idx $i rfl) rfl)
set_option hygiene false in
macro "tget3 " v:term:max : term => `(TempsHold.get hT (v := $v) (by temps_get))

end Deb2026_3784
