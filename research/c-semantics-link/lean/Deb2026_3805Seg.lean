/-
CVE-2026-3805: 修正後・修正前の証明で使う、本体の区切りと事後条件（コンパイルに時間がかかる `rfl` をここに集めた）。
-/
import Deb2026_3805Common
open CC CC.Sep CC.HProp
open Deb2026_3805_up_after
open Case5C (addr RR boolVal_ofBool_tint)
open Case4debC (IsPtr loadResult_ptr cast_ptr)

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Deb2026_3805C

/-- 引数の並びの評価（定数・一時変数・局所変数の番地・キャスト）。 -/
theorem envP_path (bp : Block) : (envP bp).get _path = some (bp, tptr tschar) := PTree.gss _ _ _

theorem envP_other (bp : Block) (id : Ident) (h : id ≠ _path) : (envP bp).get id = none := by
  unfold envP; rw [PTree.gso _path id _ _ (Ne.symm h)]; exact PTree.gempty _

macro "eval_one" : tactic => `(tactic| (first
    | rfl
    | exact EvalExpr.Econst_int _ _
    | exact EvalExpr.Etempvar _ _ _ ((‹TempsHold _ _›).get (by temps_get))
    | exact EvalExpr.Eaddrof _ _ _ _ (eval_var_local (envP_path _))
    | exact cast_ptr ‹IsPtr _› _ _ _
    | (refine EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) ?_; rfl)))

macro "eval_args" : tactic => `(tactic| (
  repeat' (first | exact EvalExprlist.nil | refine EvalExprlist.cons _ _ _ _ ?_ _ _ ?_ ?_ ?_)
  all_goals try eval_one
  all_goals try eval_one))

/-- 事後条件: CURLE_OK なら、`share` と `req->path` が別々に所有された文字列を指す。 -/
def ppPostA (c : Ctx) (v : Val) : HProp := fun hp => v = .Vint Integers.Int.zero →
  ∃ bs fs ns bq fq nq, (cD c ∗ cS c (.Vptr bs Integers.Ptrofs.zero) ∗ arr bs fs (ns + 1)
    ∗ cR c (.Vptr bq Integers.Ptrofs.zero) ∗ strAt bq fq nq) hp

def ppSpecA (c : Ctx) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _smb_conn noattr),
             tptr (Ty.Tstruct _smb_request noattr)]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.dataB c.dataO, .Vptr c.smbcB c.smbcO, .Vptr c.reqB c.reqO]
    ∧ H0 c hp
  post := ppPostA c
  measure := fun _ => 0

/-- 返る値が CURLE_OK でない return では、事後条件は何も求めない。 -/
theorem post_err (c : Ctx) (r : Integers.Int) (hr : r ≠ Integers.Int.zero) (hp : Heap) :
    ppPostA c (.Vint r) hp := fun h => absurd (vint_inj h) hr

/-! ## 本体を区切る（`n` 番目の文と、その後ろ） -/

abbrev B : Stmt := f_smb_parse_url_path.fn_body

def tl0 : Stmt := B

def tl1 : Stmt := match B with
  | .Ssequence _ (r) => r
  | _ => .Sskip

def tl2 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (r)) => r
  | _ => .Sskip

def tl3 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (r))) => r
  | _ => .Sskip

def tl4 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (r)))) => r
  | _ => .Sskip

def tl5 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (r))))) => r
  | _ => .Sskip

def tl6 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (r)))))) => r
  | _ => .Sskip

def tl7 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (r))))))) => r
  | _ => .Sskip

def tl8 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (r)))))))) => r
  | _ => .Sskip

def tl9 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (r))))))))) => r
  | _ => .Sskip

def tl10 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (r)))))))))) => r
  | _ => .Sskip

def tl11 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (r))))))))))) => r
  | _ => .Sskip

def tl12 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (r)))))))))))) => r
  | _ => .Sskip

def tl13 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (r))))))))))))) => r
  | _ => .Sskip

def hd0 : Stmt := match B with
  | .Ssequence a _ => a
  | _ => .Sskip

def hd1 : Stmt := match B with
  | .Ssequence _ (.Ssequence a _) => a
  | _ => .Sskip

def hd2 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence a _)) => a
  | _ => .Sskip

def hd3 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence a _))) => a
  | _ => .Sskip

def hd4 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence a _)))) => a
  | _ => .Sskip

def hd5 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence a _))))) => a
  | _ => .Sskip

def hd6 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence a _)))))) => a
  | _ => .Sskip

def hd7 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence a _))))))) => a
  | _ => .Sskip

def hd8 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence a _)))))))) => a
  | _ => .Sskip

def hd9 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence a _))))))))) => a
  | _ => .Sskip

def hd10 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence a _)))))))))) => a
  | _ => .Sskip

def hd11 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence a _))))))))))) => a
  | _ => .Sskip

def hd12 : Stmt := match B with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence a _)))))))))))) => a
  | _ => .Sskip

theorem tl0_B : tl0 = B := rfl

theorem split0 : tl0 = .Ssequence hd0 tl1 := rfl

theorem split1 : tl1 = .Ssequence hd1 tl2 := rfl

theorem split2 : tl2 = .Ssequence hd2 tl3 := rfl

theorem split3 : tl3 = .Ssequence hd3 tl4 := rfl

theorem split4 : tl4 = .Ssequence hd4 tl5 := rfl

theorem split5 : tl5 = .Ssequence hd5 tl6 := rfl

theorem split6 : tl6 = .Ssequence hd6 tl7 := rfl

theorem split7 : tl7 = .Ssequence hd7 tl8 := rfl

theorem split8 : tl8 = .Ssequence hd8 tl9 := rfl

theorem split9 : tl9 = .Ssequence hd9 tl10 := rfl

theorem split10 : tl10 = .Ssequence hd10 tl11 := rfl

theorem split11 : tl11 = .Ssequence hd11 tl12 := rfl

theorem split12 : tl12 = .Ssequence hd12 tl13 := rfl

theorem tl13_ret : tl13 = .Sreturn (some (.Econst_int (Integers.Int.repr 0) tint)) := rfl

abbrev RB (c : Ctx) : Sep.ExitConds :=
  { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := ppPostA c }

theorem seg (ge fe) (c : Ctx) {t h r : Stmt} (hs : t = .Ssequence h r) (P Q : Sep.Assn)
    (h1 : Triple ge fe f_smb_parse_url_path P h (RR (ppPostA c) Q))
    (h2 : Triple ge fe f_smb_parse_url_path Q r (RB c)) :
    Triple ge fe f_smb_parse_url_path P t (RB c) := by
  rw [hs]
  exact triple_seq ge fe _ P Q (RB c) _ _ h1 h2

theorem only_RR (ge fe f) {P Q : Sep.Assn} {s : Stmt} (Ret : Val → HProp)
    (h : Triple ge fe f P s (.only Q)) : Triple ge fe f P s (RR Ret Q) :=
  triple_conseq ge fe f h (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ _ x => x.elim)
    (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)

macro "tsub" : tactic => `(tactic| (
  repeat (first | exact fun _ h => absurd h (List.not_mem_nil) | refine List.forall_mem_cons.mpr ⟨?_, ?_⟩)
  all_goals temps_get))

end Deb2026_3805C
