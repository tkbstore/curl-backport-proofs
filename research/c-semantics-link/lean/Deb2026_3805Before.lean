/-
CVE-2026-3805: 上流の修正前（22b0cbe65f）の `smb_parse_url_path`（U0）と P0。

証明すること（`parse_before`）: 外部関数が決まった値を返すとき（`Curl_urldecode` は文字列 `x`、`Curl_cstrdup` は新しいブロック `y.1` の文字列、
`strchr` は `y.1` の位置 `k`）、戻り値は CURLE_OK で、`smbc->share = y.1 + 0`、`req->path = y.1 + (k+1)`（同じブロック）。
`P0_C` で、この前提を満たす具体的なメモリと値（`s/f`）があることを示す。
-/
import Deb2026_3805After
import GenDeb2026_3805UpBefore
import Case5Witness
open CC CC.Sep CC.HProp
open Deb2026_3805_up_before
open Case5C (addr RR boolVal_ofBool_tint cell mapsto_disj agrees_union)
open Case4debC (IsPtr loadResult_ptr cast_ptr)
open Deb2026_3805C

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Deb2026_3805B

theorem cenv_same : Deb2026_3805_up_before.prog.prog_comp_env = Deb2026_3805_up_after.prog.prog_comp_env := rfl

abbrev B0 : Stmt := f_smb_parse_url_path.fn_body

def tlb0 : Stmt := B0

def tlb1 : Stmt := match B0 with
  | .Ssequence _ (r) => r
  | _ => .Sskip

def tlb2 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence _ (r)) => r
  | _ => .Sskip

def tlb3 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (r))) => r
  | _ => .Sskip

def tlb4 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (r)))) => r
  | _ => .Sskip

def tlb5 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (r))))) => r
  | _ => .Sskip

def tlb6 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (r)))))) => r
  | _ => .Sskip

def tlb7 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (r))))))) => r
  | _ => .Sskip

def tlb8 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (r)))))))) => r
  | _ => .Sskip

def tlb9 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (r))))))))) => r
  | _ => .Sskip

def tlb10 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (r)))))))))) => r
  | _ => .Sskip

def tlb11 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (r))))))))))) => r
  | _ => .Sskip

def hdb0 : Stmt := match B0 with
  | .Ssequence a _ => a
  | _ => .Sskip

def hdb1 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence a _) => a
  | _ => .Sskip

def hdb2 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence _ (.Ssequence a _)) => a
  | _ => .Sskip

def hdb3 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence a _))) => a
  | _ => .Sskip

def hdb4 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence a _)))) => a
  | _ => .Sskip

def hdb5 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence a _))))) => a
  | _ => .Sskip

def hdb6 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence a _)))))) => a
  | _ => .Sskip

def hdb7 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence a _))))))) => a
  | _ => .Sskip

def hdb8 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence a _)))))))) => a
  | _ => .Sskip

def hdb9 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence a _))))))))) => a
  | _ => .Sskip

def hdb10 : Stmt := match B0 with
  | .Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence _ (.Ssequence a _)))))))))) => a
  | _ => .Sskip

theorem splitb0 : tlb0 = .Ssequence hdb0 tlb1 := rfl

theorem splitb1 : tlb1 = .Ssequence hdb1 tlb2 := rfl

theorem splitb2 : tlb2 = .Ssequence hdb2 tlb3 := rfl

theorem splitb3 : tlb3 = .Ssequence hdb3 tlb4 := rfl

theorem splitb4 : tlb4 = .Ssequence hdb4 tlb5 := rfl

theorem splitb5 : tlb5 = .Ssequence hdb5 tlb6 := rfl

theorem splitb6 : tlb6 = .Ssequence hdb6 tlb7 := rfl

theorem splitb7 : tlb7 = .Ssequence hdb7 tlb8 := rfl

theorem splitb8 : tlb8 = .Ssequence hdb8 tlb9 := rfl

theorem splitb9 : tlb9 = .Ssequence hdb9 tlb10 := rfl

theorem splitb10 : tlb10 = .Ssequence hdb10 tlb11 := rfl

theorem tl11_ret : tlb11 = .Sreturn (some (.Econst_int (Integers.Int.repr 0) tint)) := rfl


/-! ## 決まった値を返す外部関数の仕様（`Deb2026_3805C` の弱い仕様の、1つの場合） -/

def udSpecD (bp : Block) (x : PS) : FunSpec :=
  { udSpec bp with post := fun v hp => v = .Vint Integers.Int.zero
      ∧ (cP bp (.Vptr x.1 Integers.Ptrofs.zero) ∗ strAt x.1 x.2.1 x.2.2) hp }

def dupSpecD (y : PS) : FunSpec :=
  { dupSpec with post := fun v hp => v = .Vptr y.1 Integers.Ptrofs.zero ∧ strAt y.1 y.2.1 y.2.2 hp }

def chrSpecD (y : PS) (o : Integers.Ptrofs) : FunSpec :=
  { chrSpec y.1 y.2.1 y.2.2 with post := fun v hp => v = .Vptr y.1 o ∧ strAt y.1 y.2.1 y.2.2 hp }

structure ExtB (ge : CGenv) (x y : PS) (o : Integers.Ptrofs) : Prop where
  ud : ∃ b fd, Genv.findSymbol ge.genv_genv _Curl_urldecode = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr tschar, tulong, tptr (tptr tschar), tptr tulong, tint] tint cc_default
    ∧ ∀ bp vs, SatisfiesAt ge (FunctionEntry2 ge) fd (udSpecD bp x) vs
  dup : ∃ b fd, Genv.findSymbol ge.genv_genv _Curl_cstrdup = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr tschar] (tptr tschar) cc_default
    ∧ ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fd (dupSpecD y) vs
  free : ∃ b fd, Genv.findSymbol ge.genv_genv _Curl_cfree = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr tvoid] tvoid cc_default
    ∧ ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fd freeSpec vs
  chr : ∃ b fd, Genv.findSymbol ge.genv_genv _strchr = some b ∧ FuncPtr ge b fd
    ∧ typeOfFundef fd = .Tfunction [tptr tschar, tint] (tptr tschar) cc_default
    ∧ ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) fd (chrSpecD y o) vs

/-- 事後条件: 戻り値は CURLE_OK で、`share` は `y.1` の先頭、`req->path` は同じブロックの `k+1`。 -/
def ppPostB (c : Ctx) (y : PS) (k : Nat) (v : Val) : HProp := fun hp => v = .Vint Integers.Int.zero ∧
  ∃ fc o', Integers.Ptrofs.unsigned o' = ((k + 1 : Nat) : _root_.Int)
    ∧ (cD c ∗ cS c (.Vptr y.1 Integers.Ptrofs.zero) ∗ cR c (.Vptr y.1 o') ∗ arr y.1 fc (y.2.2 + 1)
       ∗ ownStr c.oldV) hp

def ppSpecB (c : Ctx) (y : PS) (k : Nat) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _smb_conn noattr),
             tptr (Ty.Tstruct _smb_request noattr)]
  tyres := tint
  cc := cc_default
  pre := fun vargs hp => vargs = [.Vptr c.dataB c.dataO, .Vptr c.smbcB c.smbcO, .Vptr c.reqB c.reqO]
    ∧ H0 c hp
  post := ppPostB c y k
  measure := fun _ => 0

abbrev RBB (c : Ctx) (y : PS) (k : Nat) : Sep.ExitConds :=
  { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := ppPostB c y k }

theorem segB (ge fe) (c : Ctx) (y : PS) (k : Nat) {t h r : Stmt} (hs : t = .Ssequence h r) (P Q : Sep.Assn)
    (h1 : Triple ge fe f_smb_parse_url_path P h (RR (ppPostB c y k) Q))
    (h2 : Triple ge fe f_smb_parse_url_path Q r (RBB c y k)) :
    Triple ge fe f_smb_parse_url_path P t (RBB c y k) := by
  rw [hs]
  exact triple_seq ge fe _ P Q (RBB c y k) _ _ h1 h2

theorem s4condB (ge : CGenv) (c : Ctx) (bp : Block) (x : PS) (H R1 R2 : HProp)
    (hpe : H = cP bp (.Vptr x.1 Integers.Ptrofs.zero) ∗ R1) (hse : H = strAt x.1 x.2.1 x.2.2 ∗ R2) (A : Stmt)
    (hA : A = .Ssequence
      (.Ssequence (.Sset _t'17 (.Evar _path (tptr tschar)))
        (.Ssequence (.Sset _t'18 (.Ederef (.Etempvar _t'17 (tptr tschar)) tschar))
          (.Sifthenelse (.Ebinop .Oeq (.Etempvar _t'18 tschar) (.Econst_int (Integers.Int.repr 47) tint) tint)
            (.Sset _t'2 (.Econst_int (Integers.Int.repr 1) tint))
            (.Ssequence (.Sset _t'19 (.Evar _path (tptr tschar)))
              (.Ssequence (.Sset _t'20 (.Ederef (.Etempvar _t'19 (tptr tschar)) tschar))
                (.Sset _t'2 (.Ecast (.Ebinop .Oeq (.Etempvar _t'20 tschar)
                  (.Econst_int (Integers.Int.repr 92) tint) tint) tbool)))))))
      (.Sifthenelse (.Etempvar _t'2 tint)
        (.Ssequence (.Sset _t'16 (.Evar _path (tptr tschar)))
          (.Sset _t'3 (.Ecast (.Ebinop .Oadd (.Etempvar _t'16 (tptr tschar))
            (.Econst_int (Integers.Int.repr 1) tint) (tptr tschar)) (tptr tschar))))
        (.Ssequence (.Sset _t'15 (.Evar _path (tptr tschar)))
          (.Sset _t'3 (.Ecast (.Etempvar _t'15 (tptr tschar)) (tptr tschar)))))) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (LocalSt (E bp) (Lk c) (H)) A
      (.only (fun e le hp => ∃ v3, IsPtr v3 ∧ LocalSt (E bp) ((_t'3, v3) :: Lk c) (H) e le hp)) := by
  subst hA
  have hpv : IsPtr (.Vptr x.1 Integers.Ptrofs.zero) := Or.inl ⟨_, _, rfl⟩
  have hc0 : 0 ≤ x.2.2 := Nat.zero_le _
  refine triple_seq_fwd ge _ _ _
    (fun e le hp => ∃ bb : Bool, LocalSt (E bp) ((_t'2, Val.ofBool bb) :: Lk c) (H) e le hp)
    _ _ _ ?a1 ?a2
  case a1 =>
    refine triple_seq_fwd ge _ _ _
      (LocalSt (E bp) ((_t'17, .Vptr x.1 Integers.Ptrofs.zero) :: Lk c) (H)) _ _ _ ?b1 ?b2
    case b1 =>
      refine set2 ge _ _ (E bp) _ _ _t'17 _ _ (by lfresh) ?_
      intro le m hp hT hH hag
      exact eval_pathvar hpe hH hag hpv
    case b2 =>
      refine triple_seq_fwd ge _ _ _
        (LocalSt (E bp) ((_t'18, .Vint (x.2.1 0)) :: (_t'17, .Vptr x.1 Integers.Ptrofs.zero) :: Lk c)
          (H)) _ _ _ ?d1 ?d2
      case d1 =>
        refine set2 ge _ _ (E bp) _ _ _t'18 _ _ (by lfresh) ?_
        intro le m hp hT hH hag
        exact eval_char_str (hT.get (by lmem)) unsigned_zero hse hH hag hc0
      case d2 =>
        refine triple_if_local ge _ _ (E bp) _ _ _ (Integers.Int.eq (x.2.1 0) (Integers.Int.repr 47)) _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Ebinop _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) (EvalExpr.Econst_int _ _) (cmp47 _ _ m),
            boolVal_ofBool_tint _ m⟩) ?_
        cases h47 : Integers.Int.eq (x.2.1 0) (Integers.Int.repr 47)
        · -- '/' でない: t'21 = path; t'22 = *t'21; t'2 = (t'22 == '\\');
          refine triple_seq_fwd ge _ _ _
            (LocalSt (E bp) ((_t'19, .Vptr x.1 Integers.Ptrofs.zero) :: (_t'18, .Vint (x.2.1 0))
              :: (_t'17, .Vptr x.1 Integers.Ptrofs.zero) :: Lk c) (H)) _ _ _ ?e1 ?e2
          case e1 =>
            refine set2 ge _ _ (E bp) _ _ _t'19 _ _ (by lfresh) ?_
            intro le m hp hT hH hag
            exact eval_pathvar hpe hH hag hpv
          case e2 =>
            refine triple_seq_fwd ge _ _ _
              (LocalSt (E bp) ((_t'20, .Vint (x.2.1 0)) :: (_t'19, .Vptr x.1 Integers.Ptrofs.zero)
                :: (_t'18, .Vint (x.2.1 0)) :: (_t'17, .Vptr x.1 Integers.Ptrofs.zero) :: Lk c)
                (H)) _ _ _ ?f1 ?f2
            case f1 =>
              refine set2 ge _ _ (E bp) _ _ _t'20 _ _ (by lfresh) ?_
              intro le m hp hT hH hag
              exact eval_char_str (hT.get (by lmem)) unsigned_zero hse hH hag hc0
            case f2 =>
              refine triple_conseq ge _ _
                (set2 ge _ _ (E bp) _ _ _t'2 _ (Val.ofBool (Integers.Int.eq (x.2.1 0) (Integers.Int.repr 92)))
                  (by lfresh) ?_) (fun _ _ _ x => x)
                (fun e le hp ⟨he, hT, hH⟩ => ⟨_, he, TempsHold_mono (by lsub) hT, hH⟩)
                (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
              intro le m hp hT _ _
              exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _
                (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) (EvalExpr.Econst_int _ _) (cmp92 _ _ m))
                (cast_bool _ m)
        · -- '/': t'2 = 1;
          refine triple_conseq ge _ _ (set2 ge _ _ (E bp) _ _ _t'2 _ (Val.ofBool true) (by lfresh) ?_)
            (fun _ _ _ x => x)
            (fun e le hp ⟨he, hT, hH⟩ => ⟨true, he, TempsHold_mono (by lsub) hT, hH⟩)
            (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
          intro le m hp hT _ _
          exact EvalExpr.Econst_int _ _
  case a2 =>
    refine triple_lift ge _ _ (fun bb : Bool => LocalSt (E bp) ((_t'2, Val.ofBool bb) :: Lk c) (H))
      _ _ _ (fun e le hp h => h) ?_
    intro bb
    refine triple_if_local ge _ _ (E bp) _ _ _ bb _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by lmem)), boolVal_ofBool_tint _ m⟩) ?_
    cases bb
    · refine triple_seq_fwd ge _ _ _
        (LocalSt (E bp) ((_t'15, .Vptr x.1 Integers.Ptrofs.zero) :: (_t'2, Val.ofBool false) :: Lk c)
          (H)) _ _ _ ?h1 ?h2
      case h1 =>
        refine set2 ge _ _ (E bp) _ _ _t'15 _ _ (by lfresh) ?_
        intro le m hp hT hH hag
        exact eval_pathvar hpe hH hag hpv
      case h2 =>
        refine triple_conseq ge _ _ (set2 ge _ _ (E bp) _ _ _t'3 _ (.Vptr x.1 Integers.Ptrofs.zero) (by lfresh) ?_)
          (fun _ _ _ x => x)
          (fun e le hp ⟨he, hT, hH⟩ => ⟨_, hpv, he, TempsHold_mono (by lsub) hT, hH⟩)
          (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
        intro le m hp hT _ _
        exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) (cast_ptr hpv _ _ m)
    · refine triple_seq_fwd ge _ _ _
        (LocalSt (E bp) ((_t'16, .Vptr x.1 Integers.Ptrofs.zero) :: (_t'2, Val.ofBool true) :: Lk c)
          (H)) _ _ _ ?h1 ?h2
      case h1 =>
        refine set2 ge _ _ (E bp) _ _ _t'16 _ _ (by lfresh) ?_
        intro le m hp hT hH hag
        exact eval_pathvar hpe hH hag hpv
      case h2 =>
        refine triple_conseq ge _ _ (set2 ge _ _ (E bp) _ _ _t'3 _
            (.Vptr x.1 (Integers.Ptrofs.add Integers.Ptrofs.zero
              (Integers.Ptrofs.mul (Integers.Ptrofs.repr (sizeof ge.genv_cenv tschar))
                (Cop.ptrofsOfInt .Signed (Integers.Int.repr 1))))) (by lfresh) ?_)
          (fun _ _ _ x => x)
          (fun e le hp ⟨he, hT, hH⟩ => ⟨_, Or.inl ⟨_, _, rfl⟩, he, TempsHold_mono (by lsub) hT, hH⟩)
          (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
        intro le m hp hT _ _
        exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) (EvalExpr.Econst_int _ _)
          (semAdd_ptr_int _ _ _ _ _ rfl)) (cast_ptr (Or.inl ⟨_, _, rfl⟩) _ _ m)


section
variable (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx) (bp : Block)
  (x y : PS) (k : Nat) (o : Integers.Ptrofs) (X : ExtB ge x y o)
include hcenv X

abbrev K1 : HProp := cD c ∗ cS c c.oldV ∗ ownStr c.oldV ∗ cR c c.reqV ∗ emp

abbrev HB1 : HProp := (cP bp (.Vptr x.1 Integers.Ptrofs.zero) ∗ strAt x.1 x.2.1 x.2.2) ∗ K1 c

theorem b0 (hup : IsPtr c.upV) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path
      (LocalSt (E bp) (Lk c) (H0 c ∗ Case3C.Locs [(bp, 8)])) hdb0
      (RR (ppPostB c y k) (LocalSt (E bp) ((_result, .Vint Integers.Int.zero) :: Lk c) (HB1 c bp x))) := by
  have hc := hcenv.trans cenv_same
  obtain ⟨bU, fdU, hsU, hfU, htU, hU⟩ := X.ud
  refine only_RR _ _ _ _ ?_
  have hcell : H0 c ∗ Case3C.Locs [(bp, 8)]
      = mapsto Mptr .Freeable c.dataB (Integers.Ptrofs.unsigned c.dataO) c.upV
        ∗ (cS c c.oldV ∗ ownStr c.oldV ∗ cR c c.reqV ∗ Case3C.Locs [(bp, 8)]) := by
    unfold H0 cD; ac_rfl
  have hre : H0 c ∗ Case3C.Locs [(bp, 8)] = anyBytes .Freeable bp 0 8 ∗ K1 c := by
    simp only [H0, Case3C.Locs, K1]; ac_rfl
  refine triple_seq_fwd ge _ _ _
    (fun e le hp => ∃ v, LocalSt (E bp) ((_t'1, v) :: (_t'21, c.upV) :: Lk c)
      ((udSpecD bp x).post v ∗ K1 c) e le hp) _ _ _
    (triple_seq_fwd ge _ _ _ (LocalSt (E bp) ((_t'21, c.upV) :: Lk c) (H0 c ∗ Case3C.Locs [(bp, 8)]))
      _ _ _ ?a ?b) ?c
  case a =>
    refine set2 ge _ _ (E bp) _ _ _t'21 _ c.upV (by lfresh) ?_
    intro le m hp hT hH hag
    exact eval_load (lv_upPath (b := c.dataB) (o := c.dataO) hc (hT.get (by lmem))) rfl
      (cell_load hcell hH hag hup)
  case b =>
    rw [hre]
    refine call2 ge _ _ (udSpecD bp x) _t'1 _ _ (E bp) _ (anyBytes .Freeable bp 0 8) (K1 c)
      [c.upV, .Vlong (Integers.Int64.repr 0), .Vptr bp Integers.Ptrofs.zero,
       .Vlong (Integers.Int64.repr 0), .Vint (Integers.Int.repr 3)] bU fdU
      (hU bp) hfU htU ?hcl (by lfresh) ?cal ?args (fun h hh => hh)
    case hcl => rfl
    case cal => exact fun _ _ _ => eval_callee_global (envP_other _ _ (by decide)) hsU rfl
    case args =>
      intro le m hT
      dsimp only [udSpecD, udSpec]
      eval_args2
  case c =>
    refine triple_lift ge _ _ (fun v => LocalSt (E bp) ((_t'1, v) :: (_t'21, c.upV) :: Lk c)
      ((udSpecD bp x).post v ∗ K1 c)) _ _ _ (fun e le hp h => h) ?_
    intro v
    refine lift_and ge _ _ (E bp) _ _ _ _ _ _ ?_
    intro hv; subst hv
    refine triple_conseq ge _ _ (set2 ge _ _ (E bp) _ _ _result _ (.Vint Integers.Int.zero) (by lfresh) ?_)
      (fun _ _ _ x => x) (fun e le hp ⟨he, hT, hH⟩ => ⟨he, TempsHold_mono (by lsub) hT, hH⟩)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
    intro le m hp hT _ _
    exact EvalExpr.Etempvar _ _ _ (hT.get (by lmem))

theorem b1 :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path
      (LocalSt (E bp) ((_result, .Vint Integers.Int.zero) :: Lk c) (HB1 c bp x)) hdb1
      (RR (ppPostB c y k) (LocalSt (E bp) (Lk c) (HB1 c bp x))) := by
  refine triple_if_local ge _ _ (E bp) _ _ _ false _ _ _ ?_ ?_
  · intro le m hp hT _ _
    exact ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by lmem)), rfl⟩
  · exact triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x)
      (fun e le hp ⟨he, hT, hH⟩ => ⟨he, TempsHold_mono (by lsub) hT, hH⟩)
      (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)

abbrev HB2 : HProp :=
  cS c (.Vptr y.1 Integers.Ptrofs.zero) ∗ strAt y.1 y.2.1 y.2.2 ∗ ownStr c.oldV
    ∗ cP bp (.Vptr x.1 Integers.Ptrofs.zero) ∗ strAt x.1 x.2.1 x.2.2 ∗ cD c ∗ cR c c.reqV ∗ emp

theorem b2 :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (LocalSt (E bp) (Lk c) (HB1 c bp x)) hdb2
      (RR (ppPostB c y k) (LocalSt (E bp) (Lk c) (HB2 c bp x y))) := by
  have hc := hcenv.trans cenv_same
  obtain ⟨bD, fdD, hsD, hfD, htD, hD⟩ := X.dup
  refine only_RR _ _ _ _ ?_
  have hpe : HB1 c bp x = cP bp (.Vptr x.1 Integers.Ptrofs.zero)
      ∗ (strAt x.1 x.2.1 x.2.2 ∗ K1 c) := by unfold HB1; ac_rfl
  have hse : HB1 c bp x = strAt x.1 x.2.1 x.2.2
      ∗ (cP bp (.Vptr x.1 Integers.Ptrofs.zero) ∗ K1 c) := by unfold HB1; ac_rfl
  refine triple_seq_fwd ge _ _ _
    (fun e le hp => ∃ v4, LocalSt (E bp) ((_t'4, v4) :: Lk c) ((dupSpecD y).post v4 ∗ HB1 c bp x) e le hp)
    _ _ _ ?a ?b
  case a =>
    refine triple_seq_fwd ge _ _ _ _ _ _ _ (s4condB ge c bp x _ _ _ hpe hse _ rfl) ?_
    refine triple_lift ge _ _ (fun v3 : Val => fun e le hp => IsPtr v3
        ∧ LocalSt (E bp) ((_t'3, v3) :: Lk c) (HB1 c bp x) e le hp) _ _ _ (fun e le hp h => h) ?_
    intro v3
    refine Case1C.triple_pure ge _ _ _ _ _ _ ?_
    intro hv3
    refine heap_eq ge _ _ _ _ _ (emp ∗ HB1 c bp x) _ _ (emp_sep_eq _).symm ?_
    refine triple_conseq ge _ _
      (call2 ge _ _ (dupSpecD y) _t'4 _ _ (E bp) _ emp (HB1 c bp x) [v3] bD fdD hD hfD htD ?hcl (by lfresh)
        ?cal ?args (fun h hh => hh))
      (fun _ _ _ x => x) (fun e le hp ⟨v, he, hT, hH⟩ => ⟨v, he, TempsHold_mono (by lsub) hT, hH⟩)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
    case hcl => rfl
    case cal => exact fun _ _ _ => eval_callee_global (envP_other _ _ (by decide)) hsD rfl
    case args =>
      intro le m hT
      exact .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) (cast_ptr hv3 _ _ m) .nil
  case b =>
    refine triple_lift ge _ _ (fun v4 : Val => LocalSt (E bp) ((_t'4, v4) :: Lk c)
      ((dupSpecD y).post v4 ∗ HB1 c bp x)) _ _ _ (fun e le hp h => h) ?_
    intro v4
    refine lift_and ge _ _ (E bp) _ _ _ _ _ _ ?_
    intro hv; subst hv
    have he : strAt y.1 y.2.1 y.2.2 ∗ HB1 c bp x
        = mapsto Mptr .Freeable c.smbcB (Integers.Ptrofs.unsigned c.smbcO) c.oldV
          ∗ (strAt y.1 y.2.1 y.2.2 ∗ ownStr c.oldV ∗ cP bp (.Vptr x.1 Integers.Ptrofs.zero)
             ∗ strAt x.1 x.2.1 x.2.2 ∗ cD c ∗ cR c c.reqV ∗ emp) := by
      simp only [HB1, K1, cS]; ac_rfl
    rw [he]
    refine triple_conseq ge _ _
      (assign_cell ge _ _ (E bp) _ _ _ _ Mptr c.smbcB c.smbcO _ c.oldV (.Vptr y.1 Integers.Ptrofs.zero)
        rfl rfl ?lv ?ev)
      (fun _ _ _ x => x) (fun e le hp ⟨he, hT, hH⟩ => ⟨he, TempsHold_mono (by lsub) hT, hH⟩)
      (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
    case lv => exact fun le m hT => lv_share hc (hT.get (by lmem))
    case ev => exact fun le m hT => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by lmem)),
      cast_ptr (Or.inl ⟨_, _, rfl⟩) _ _ m⟩

abbrev HB4 : HProp :=
  cS c (.Vptr y.1 Integers.Ptrofs.zero) ∗ strAt y.1 y.2.1 y.2.2 ∗ ownStr c.oldV ∗ cR c c.reqV ∗ cD c
    ∗ Case3C.Locs [(bp, 8)]

theorem b3 :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (LocalSt (E bp) (Lk c) (HB2 c bp x y)) hdb3
      (RR (ppPostB c y k) (LocalSt (E bp) (Lk c) (HB4 c bp y))) := by
  obtain ⟨bF, fdF, hsF, hfF, htF, hF⟩ := X.free
  refine only_RR _ _ _ _ ?_
  have hpv : IsPtr (.Vptr x.1 Integers.Ptrofs.zero) := Or.inl ⟨_, _, rfl⟩
  have hp1 : HB2 c bp x y = cP bp (.Vptr x.1 Integers.Ptrofs.zero)
      ∗ (cS c (.Vptr y.1 Integers.Ptrofs.zero) ∗ strAt y.1 y.2.1 y.2.2 ∗ ownStr c.oldV ∗ strAt x.1 x.2.1 x.2.2
         ∗ cD c ∗ cR c c.reqV ∗ emp) := by unfold HB2; ac_rfl
  have hp2 : HB2 c bp x y = strAt x.1 x.2.1 x.2.2
      ∗ (cS c (.Vptr y.1 Integers.Ptrofs.zero) ∗ strAt y.1 y.2.1 y.2.2 ∗ ownStr c.oldV
         ∗ cP bp (.Vptr x.1 Integers.Ptrofs.zero) ∗ cD c ∗ cR c c.reqV ∗ emp) := by unfold HB2; ac_rfl
  refine triple_seq_fwd ge _ _ _
    (LocalSt (E bp) ((_t'14, .Vptr x.1 Integers.Ptrofs.zero) :: Lk c) (HB2 c bp x y)) _ _ _ ?a ?b
  case a =>
    refine set2 ge _ _ (E bp) _ _ _t'14 _ _ (by lfresh) ?_
    intro le m hp hT hH hag
    exact eval_pathvar hp1 hH hag hpv
  case b =>
    rw [hp2]
    refine triple_conseq ge _ _
      (call_none ge _ _ freeSpec _ _ (E bp) _ (strAt x.1 x.2.1 x.2.2) _ [.Vptr x.1 Integers.Ptrofs.zero]
        bF fdF hF hfF htF ?hcl ?cal ?args
        (fun h hh => ⟨_, rfl, Or.inr ⟨x.1, x.2.1, x.2.2, rfl, hh⟩⟩) (fun _ _ hh => hh))
      (fun _ _ _ x => x) (fun e le hp ⟨he, hT, hH⟩ => ⟨he, TempsHold_mono (by lsub) hT, ?hh⟩)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
    case hcl => rfl
    case cal => exact fun _ _ _ => eval_callee_global (envP_other _ _ (by decide)) hsF rfl
    case args =>
      intro le m hT
      exact .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) (cast_ptr hpv _ _ m) .nil
    case hh =>
      have h5 : HB4 c bp y = cS c (.Vptr y.1 Integers.Ptrofs.zero) ∗ strAt y.1 y.2.1 y.2.2 ∗ ownStr c.oldV
          ∗ anyBytes .Freeable bp 0 8 ∗ cD c ∗ cR c c.reqV ∗ emp := by
        simp only [HB4, Case3C.Locs]; ac_rfl
      show HB4 c bp y hp
      rw [h5]
      exact sep_mono (entails_refl _) (sep_mono (entails_refl _) (sep_mono (entails_refl _)
        (sep_mono (fun h hh => mapsto_any hh) (entails_refl _)))) _ hH

theorem shareB4 : HB4 c bp y = mapsto Mptr .Freeable c.smbcB (Integers.Ptrofs.unsigned c.smbcO)
    (.Vptr y.1 Integers.Ptrofs.zero) ∗ (strAt y.1 y.2.1 y.2.2 ∗ ownStr c.oldV ∗ cR c c.reqV ∗ cD c
      ∗ Case3C.Locs [(bp, 8)]) := by unfold HB4 cS; ac_rfl

theorem strB4 : HB4 c bp y = strAt y.1 y.2.1 y.2.2 ∗ (cS c (.Vptr y.1 Integers.Ptrofs.zero) ∗ ownStr c.oldV
    ∗ cR c c.reqV ∗ cD c ∗ Case3C.Locs [(bp, 8)]) := by unfold HB4; ac_rfl

theorem b4 :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (LocalSt (E bp) (Lk c) (HB4 c bp y)) hdb4
      (RR (ppPostB c y k) (LocalSt (E bp) (Lk c) (HB4 c bp y))) := by
  have hc := hcenv.trans cenv_same
  have hpv : IsPtr (.Vptr y.1 Integers.Ptrofs.zero) := Or.inl ⟨_, _, rfl⟩
  refine triple_seq ge _ _ _ (LocalSt (E bp) ((_t'13, .Vptr y.1 Integers.Ptrofs.zero) :: Lk c) (HB4 c bp y))
    _ _ _ (only_RR _ _ _ _ ?_) ?b
  · refine set2 ge _ _ (E bp) _ _ _t'13 _ _ (by lfresh) ?_
    intro le m hp hT hH hag
    exact eval_load (lv_share (b := c.smbcB) (o := c.smbcO) hc (hT.get (by lmem))) rfl
      (cell_load (shareB4 ge hcenv c bp x y o X) hH hag hpv)
  case b =>
    refine triple_if_local ge _ _ (E bp) _ _ _ false _ _ _ ?_ ?_
    · intro le m hp hT hH hag
      refine ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) (notbool_ptr ?_),
        boolVal_ofBool_tint _ m⟩
      rw [unsigned_zero]
      exact valid_str (strB4 ge hcenv c bp x y o X) hH hag (Nat.zero_le _)
    · exact triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x)
        (fun e le hp ⟨he, hT, hH⟩ => ⟨he, TempsHold_mono (by lsub) hT, hH⟩)
        (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)

theorem b5 :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (LocalSt (E bp) (Lk c) (HB4 c bp y)) hdb5
      (RR (ppPostB c y k) (LocalSt (E bp) ((_slash, .Vptr y.1 o) :: Lk c) (HB4 c bp y))) := by
  have hc := hcenv.trans cenv_same
  obtain ⟨bC, fdC, hsC, hfC, htC, hC⟩ := X.chr
  refine only_RR _ _ _ _ ?_
  have hpv : IsPtr (.Vptr y.1 Integers.Ptrofs.zero) := Or.inl ⟨_, _, rfl⟩
  refine triple_seq_fwd ge _ _ _
    (fun e le hp => ∃ w, LocalSt (E bp) ((_t'5, w) :: (_t'12, .Vptr y.1 Integers.Ptrofs.zero) :: Lk c)
      ((chrSpecD y o).post w ∗ (cS c (.Vptr y.1 Integers.Ptrofs.zero) ∗ ownStr c.oldV ∗ cR c c.reqV ∗ cD c
        ∗ Case3C.Locs [(bp, 8)])) e le hp) _ _ _
    (triple_seq_fwd ge _ _ _ (LocalSt (E bp) ((_t'12, .Vptr y.1 Integers.Ptrofs.zero) :: Lk c) (HB4 c bp y))
      _ _ _ ?a ?b) ?c
  case a =>
    refine set2 ge _ _ (E bp) _ _ _t'12 _ _ (by lfresh) ?_
    intro le m hp hT hH hag
    exact eval_load (lv_share (b := c.smbcB) (o := c.smbcO) hc (hT.get (by lmem))) rfl
      (cell_load (shareB4 ge hcenv c bp x y o X) hH hag hpv)
  case b =>
    rw [strB4 ge hcenv c bp x y o X]
    refine call2 ge _ _ (chrSpecD y o) _t'5 _ _ (E bp) _ (strAt y.1 y.2.1 y.2.2) _
      [.Vptr y.1 Integers.Ptrofs.zero, .Vint (Integers.Int.repr 47)] bC fdC hC hfC htC ?hcl (by lfresh) ?cal ?args
      (fun h hh => ⟨⟨_, rfl⟩, hh⟩)
    case hcl => rfl
    case cal => exact fun _ _ _ => eval_callee_global (envP_other _ _ (by decide)) hsC rfl
    case args =>
      intro le m hT
      exact .cons _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem)))
        (cast_ptr hpv _ _ m) (.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl .nil)
  case c =>
    refine triple_lift ge _ _ (fun w => LocalSt (E bp) ((_t'5, w) :: (_t'12, .Vptr y.1 Integers.Ptrofs.zero)
      :: Lk c) ((chrSpecD y o).post w ∗ (cS c (.Vptr y.1 Integers.Ptrofs.zero) ∗ ownStr c.oldV ∗ cR c c.reqV
        ∗ cD c ∗ Case3C.Locs [(bp, 8)]))) _ _ _ (fun e le hp h => h) ?_
    intro w
    refine lift_and ge _ _ (E bp) _ _ _ _ _ _ ?_
    intro hv; subst hv
    refine triple_conseq ge _ _ (set2 ge _ _ (E bp) _ _ _slash _ (.Vptr y.1 o) (by lfresh) ?_)
      (fun _ _ _ x => x) (fun e le hp ⟨he, hT, hH⟩ => ⟨he, TempsHold_mono (by lsub) hT, by
        show HB4 c bp y hp; rw [strB4 ge hcenv c bp x y o X]; exact hH⟩)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
    intro le m hp hT _ _
    exact EvalExpr.Etempvar _ _ _ (hT.get (by lmem))

theorem b67 (hk : k < y.2.2) (ho : Integers.Ptrofs.unsigned o = (k : _root_.Int)) (s1 s2 : Stmt)
    (hs : s2 = .Sskip) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path
      (LocalSt (E bp) ((_slash, .Vptr y.1 o) :: Lk c) (HB4 c bp y))
      (.Sifthenelse (.Eunop .Onotbool (.Etempvar _slash (tptr tschar)) tint) s1 s2)
      (RR (ppPostB c y k) (LocalSt (E bp) ((_slash, .Vptr y.1 o) :: Lk c) (HB4 c bp y))) := by
  subst hs
  refine triple_if_local ge _ _ (E bp) _ _ _ false _ _ _ ?_ ?_
  · intro le m hp hT hH hag
    refine ⟨_, EvalExpr.Eunop _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) (notbool_ptr ?_),
      boolVal_ofBool_tint _ m⟩
    rw [ho]
    exact valid_str (strB4 ge hcenv c bp x y o X) hH hag (Nat.le_of_lt hk)
  · exact triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x) (fun _ _ _ x => x)
      (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)

abbrev R8 : HProp :=
  cS c (.Vptr y.1 Integers.Ptrofs.zero) ∗ ownStr c.oldV ∗ cR c c.reqV ∗ cD c ∗ Case3C.Locs [(bp, 8)]

theorem b8 (hk : k < y.2.2) (ho : Integers.Ptrofs.unsigned o = (k : _root_.Int)) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path
      (LocalSt (E bp) ((_slash, .Vptr y.1 o) :: Lk c) (HB4 c bp y)) hdb8
      (RR (ppPostB c y k) (LocalSt (E bp) ((_slash, .Vptr y.1 (inc1 ge.genv_cenv o)) :: Lk c)
        (arr y.1 (upd y.2.1 k Integers.Int.zero) (y.2.2 + 1) ∗ R8 c bp y))) := by
  refine only_RR _ _ _ _ ?_
  have he : HB4 c bp y = (⌜Tail y.2.1 0 y.2.2⌝ ∗ arr y.1 y.2.1 (y.2.2 + 1)) ∗ R8 c bp y := by
    unfold HB4 R8 strAt; ac_rfl
  rw [he]
  refine lift_pure ge _ _ (E bp) _ _ _ _ _ _ ?_
  intro ht
  refine triple_seq_fwd ge _ _ _
    (LocalSt (E bp) ((_slash, .Vptr y.1 (inc1 ge.genv_cenv o)) :: (_t'7, .Vptr y.1 o) :: Lk c)
      (arr y.1 y.2.1 (y.2.2 + 1) ∗ R8 c bp y)) _ _ _
    (triple_seq_fwd ge _ _ _
      (LocalSt (E bp) ((_t'7, .Vptr y.1 o) :: (_slash, .Vptr y.1 o) :: Lk c)
        (arr y.1 y.2.1 (y.2.2 + 1) ∗ R8 c bp y)) _ _ _ ?a ?b) ?c
  case a =>
    refine set2 ge _ _ (E bp) _ _ _t'7 _ _ (by lfresh) ?_
    intro le m hp hT _ _
    exact EvalExpr.Etempvar _ _ _ (hT.get (by lmem))
  case b =>
    refine triple_set_local ge _ _ (E bp) _ ((_t'7, .Vptr y.1 o) :: Lk c) _ _slash _ _ (by lsub) (by lfresh) ?_
    intro le m hp hT _ _
    exact EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem))) (EvalExpr.Econst_int _ _)
      (semAdd_ptr_int _ _ _ _ _ rfl)
  case c =>
    refine triple_conseq ge _ _
      (assign_byte ge _ _ (E bp) _ _ _ _ y.1 o y.2.1 (y.2.2 + 1) k Integers.Int.zero (by omega) rfl ho ?lv ?ev)
      (fun _ _ _ x => x) (fun e le hp ⟨he, hT, hH⟩ => ⟨he, TempsHold_mono (by lsub) hT, hH⟩)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
    case lv => exact fun le m hT => EvalLvalue.Ederef _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by lmem)))
    case ev => exact fun le m hT => ⟨_, EvalExpr.Econst_int _ _, rfl⟩

abbrev R10 : HProp :=
  cR c (.Vptr y.1 (inc1 ge.genv_cenv o)) ∗ cS c (.Vptr y.1 Integers.Ptrofs.zero) ∗ ownStr c.oldV ∗ cD c
    ∗ Case3C.Locs [(bp, 8)]

theorem b9 :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path
      (LocalSt (E bp) ((_slash, .Vptr y.1 (inc1 ge.genv_cenv o)) :: Lk c)
        (arr y.1 (upd y.2.1 k Integers.Int.zero) (y.2.2 + 1) ∗ R8 c bp y)) hdb9
      (RR (ppPostB c y k) (LocalSt (E bp) ((_slash, .Vptr y.1 (inc1 ge.genv_cenv o)) :: Lk c)
        (arr y.1 (upd y.2.1 k Integers.Int.zero) (y.2.2 + 1) ∗ R10 ge c bp y o))) := by
  have hc := hcenv.trans cenv_same
  refine only_RR _ _ _ _ ?_
  have he : arr y.1 (upd y.2.1 k Integers.Int.zero) (y.2.2 + 1) ∗ R8 c bp y
      = mapsto Mptr .Freeable c.reqB (Integers.Ptrofs.unsigned c.reqO) c.reqV
        ∗ (arr y.1 (upd y.2.1 k Integers.Int.zero) (y.2.2 + 1) ∗ cS c (.Vptr y.1 Integers.Ptrofs.zero)
           ∗ ownStr c.oldV ∗ cD c ∗ Case3C.Locs [(bp, 8)]) := by
    simp only [R8, cR]; ac_rfl
  rw [he]
  refine triple_conseq ge _ _
    (assign_cell ge _ _ (E bp) _ _ _ _ Mptr c.reqB c.reqO _ c.reqV (.Vptr y.1 (inc1 ge.genv_cenv o))
      rfl rfl ?lv ?ev)
    (fun _ _ _ x => x) (fun e le hp ⟨he, hT, hH⟩ => ⟨he, hT, by
      show (arr y.1 (upd y.2.1 k Integers.Int.zero) (y.2.2 + 1) ∗ R10 ge c bp y o) hp
      have : arr y.1 (upd y.2.1 k Integers.Int.zero) (y.2.2 + 1) ∗ R10 ge c bp y o
          = mapsto Mptr .Freeable c.reqB (Integers.Ptrofs.unsigned c.reqO) (.Vptr y.1 (inc1 ge.genv_cenv o))
            ∗ (arr y.1 (upd y.2.1 k Integers.Int.zero) (y.2.2 + 1) ∗ cS c (.Vptr y.1 Integers.Ptrofs.zero)
               ∗ ownStr c.oldV ∗ cD c ∗ Case3C.Locs [(bp, 8)]) := by
        simp only [R10, cR]; ac_rfl
      rw [this]; exact hH⟩)
    (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
  case lv => exact fun le m hT => lv_reqPath hc (hT.get (by lmem))
  case ev => exact fun le m hT => ⟨_, EvalExpr.Etempvar _ _ _ (hT.get (by lmem)), cast_ptr (Or.inl ⟨_, _, rfl⟩) _ _ m⟩

theorem b10 (hk : k < y.2.2) (ho : Integers.Ptrofs.unsigned o = (k : _root_.Int)) (ht : Tail y.2.1 0 y.2.2) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path
      (LocalSt (E bp) ((_slash, .Vptr y.1 (inc1 ge.genv_cenv o)) :: Lk c)
        (arr y.1 (upd y.2.1 k Integers.Int.zero) (y.2.2 + 1) ∗ R10 ge c bp y o)) hdb10
      (RR (ppPostB c y k) (scanOut (E bp) (Lk c) (R10 ge c bp y o) _slash y.1 y.2.2)) := by
  refine only_RR _ _ _ _ ?_
  have ho1 : Integers.Ptrofs.unsigned (inc1 ge.genv_cenv o) = ((k + 1 : Nat) : _root_.Int) :=
    incr_ofs _ o k ho (by have := ht.2.2.2.2; omega)
  refine triple_conseq ge _ _
    (scan_loop ge _ _ (E bp) (Lk c) (R10 ge c bp y o) _slash _t'9 _t'8 y.1 y.2.2 (by lfresh3) (by decide)
      (by decide) (by decide) (y.2.2 - (k + 1)))
    ?pre (fun _ _ _ x => x) (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)
  intro e le hp hL
  refine ⟨upd y.2.1 k Integers.Int.zero, inc1 ge.genv_cenv o, by omega, ?_, ?_, hL⟩
  · rw [ho1]; congr 1; omega
  · rw [show y.2.2 - (y.2.2 - (k + 1)) = k + 1 by omega]; exact tail_cut ht hk

theorem b11 (ho : Integers.Ptrofs.unsigned o = (k : _root_.Int)) (ht : Tail y.2.1 0 y.2.2) (hk : k < y.2.2) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path (scanOut (E bp) (Lk c) (R10 ge c bp y o) _slash y.1 y.2.2)
      tlb11 (RBB c y k) := by
  rw [tl11_ret]
  have ho1 : Integers.Ptrofs.unsigned (inc1 ge.genv_cenv o) = ((k + 1 : Nat) : _root_.Int) :=
    incr_ofs _ o k ho (by have := ht.2.2.2.2; omega)
  refine triple_lift ge _ _ (fun z : (Nat → Integers.Int) × Integers.Ptrofs => LocalSt (E bp)
    ((_slash, .Vptr y.1 z.2) :: Lk c) (arr y.1 z.1 (y.2.2 + 1) ∗ R10 ge c bp y o)) _ _ _
    (fun e le hp ⟨fc, o2, h⟩ => ⟨(fc, o2), h⟩) ?_
  intro ⟨fc, o2⟩
  have h1 : arr y.1 fc (y.2.2 + 1) ∗ R10 ge c bp y o = (cD c ∗ cS c (.Vptr y.1 Integers.Ptrofs.zero)
      ∗ cR c (.Vptr y.1 (inc1 ge.genv_cenv o)) ∗ arr y.1 fc (y.2.2 + 1) ∗ ownStr c.oldV)
      ∗ Case3C.Locs [(bp, 8)] := by
    unfold R10; ac_rfl
  rw [h1]
  exact ret_here ge _ _ (hcenv.trans cenv_same) bp _ _ _ _ _ _ _ (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)
    (fun _ => rfl) (fun hp hH => ⟨rfl, fc, inc1 ge.genv_cenv o, ho1, hH⟩)

theorem body_before (hup : IsPtr c.upV) (hk : k < y.2.2) (ho : Integers.Ptrofs.unsigned o = (k : _root_.Int))
    (ht : Tail y.2.1 0 y.2.2) :
    Triple ge (FunctionEntry2 ge) f_smb_parse_url_path
      (LocalSt (envP bp) (Lb c) (H0 c ∗ Case3C.Locs [(bp, 8)])) f_smb_parse_url_path.fn_body
      { normal := Sep.Assn.no, brk := Sep.Assn.no, cont := Sep.Assn.no, ret := ppPostB c y k } := by
  show Triple _ _ _ _ tlb0 (RBB c y k)
  refine segB _ _ c y k splitb0 _ _ (b0 ge hcenv c bp x y k o X hup) ?_
  refine segB _ _ c y k splitb1 _ _ (b1 ge hcenv c bp x y k o X) ?_
  refine segB _ _ c y k splitb2 _ _ (b2 ge hcenv c bp x y k o X) ?_
  refine segB _ _ c y k splitb3 _ _ (b3 ge hcenv c bp x y k o X) ?_
  refine segB _ _ c y k splitb4 _ _ (b4 ge hcenv c bp x y k o X) ?_
  refine segB _ _ c y k splitb5 _ _ (b5 ge hcenv c bp x y k o X) ?_
  refine segB _ _ c y k splitb6 _ _ (b67 ge hcenv c bp x y k o X hk ho _ _ rfl) ?_
  refine segB _ _ c y k splitb7 _ _ (b67 ge hcenv c bp x y k o X hk ho _ _ rfl) ?_
  refine segB _ _ c y k splitb8 _ _ (b8 ge hcenv c bp x y k o X hk ho) ?_
  refine segB _ _ c y k splitb9 _ _ (b9 ge hcenv c bp x y k o X) ?_
  refine segB _ _ c y k splitb10 _ _ (b10 ge hcenv c bp x y k o X hk ho ht) ?_
  exact b11 ge hcenv c bp x y k o X ho ht hk

end

end Deb2026_3805B

namespace Deb2026_3805B
open Deb2026_3805C

theorem ppB_entry_wf :
    listNorepet (varNames f_smb_parse_url_path.fn_vars)
    ∧ listNorepet (varNames f_smb_parse_url_path.fn_params)
    ∧ listDisjoint (varNames f_smb_parse_url_path.fn_params) (varNames f_smb_parse_url_path.fn_temps) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **修正前の `smb_parse_url_path`（U0）**: 外部関数が決まった値を返すとき、CURLE_OK を返し、`req->path` は `share` と同じブロックを指す。 -/
theorem parse_before (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (c : Ctx) (x y : PS) (k : Nat)
    (o : Integers.Ptrofs) (X : ExtB ge x y o) (hup : IsPtr c.upV) (hk : k < y.2.2)
    (ho : Integers.Ptrofs.unsigned o = (k : _root_.Int)) (ht : Tail y.2.1 0 y.2.2) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_smb_parse_url_path) (ppSpecB c y k) vs := by
  by_cases hvs : vs = [.Vptr c.dataB c.dataO, .Vptr c.smbcB c.smbcO, .Vptr c.reqB c.reqO]
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  obtain ⟨hnv, hnp, hdisj⟩ := ppB_entry_wf
  refine satisfies_internal ge (FunctionEntry2 ge) f_smb_parse_url_path _ _
    (fun e le hp => ∃ bp, LocalSt (envP bp) (Lb c) (H0 c ∗ Case3C.Locs [(bp, 8)]) e le hp)
    (fun m hp hf hpre hd hag => ?_)
    (triple_lift ge _ _ _ _ _ _ (fun e le hp h => h)
      (fun bp => body_before ge hcenv c bp x y k o X hup hk ho ht))
  let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv (tptr tschar))
  have hav : AllocVariables ge.genv_cenv emptyEnv m f_smb_parse_url_path.fn_vars (envP a1.2) a1.1 :=
    .cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _)
  obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav hnv
    (by
      intro v hv
      simp only [f_smb_parse_url_path, List.mem_cons, List.mem_nil_iff, or_false] at hv
      subst hv; rw [hcenv]; decide)
    (Heap.union hp hf) hag
  have hL : Case3C.Locs [(a1.2, 8)] hl := by
    have := Case3C.locs_of_localsAt ge.genv_cenv _ _ hl hloc
    rw [hcenv] at this
    exact this
  obtain ⟨dph, dfh⟩ := Heap.disjoint_union_left.mp hdl
  refine ⟨envP a1.2,
    PTree.set _req (.Vptr c.reqB c.reqO) (PTree.set _smbc (.Vptr c.smbcB c.smbcO)
      (PTree.set _data (.Vptr c.dataB c.dataO) (createUndefTemps f_smb_parse_url_path.fn_temps))),
    a1.1, hl, FunctionEntry2.intro hnv hnp hdisj hav rfl,
    Heap.disjoint_union_left.mpr ⟨hd, Heap.disjoint_comm dfh⟩, ?_, ?_⟩
  · rw [Heap.union_assoc, Heap.union_comm (Heap.disjoint_comm dfh), ← Heap.union_assoc]
    exact hagl
  · refine ⟨a1.2, rfl, ?_, ⟨hp, hl, dph, rfl, hpre.2, hL⟩⟩
    exact TempsHold_cons (PTree.gss _ _ _)
      (TempsHold_cons ((PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _))
        (TempsHold_cons ((PTree.gso _ _ _ _ (by decide)).trans ((PTree.gso _ _ _ _ (by decide)).trans
          (PTree.gss _ _ _))) (TempsHold_nil _)))

/-! ## P0 の具体的な入力

  メモリ（1つのブロック、24 バイト）: 0 に `data->state.up.path`、8 に `smbc->share`、16 に `req->path`（どれも NULL）。
  外部関数: `Curl_cstrdup` は文字列 `s/f`（ブロック `y.1`）を返し、`strchr(share, '/')` は `y.1 + 1` を返す。
-/

def fS (i : Nat) : Integers.Int :=
  if i = 0 then Integers.Int.repr 115 else if i = 1 then Integers.Int.repr 47
  else if i = 2 then Integers.Int.repr 102 else Integers.Int.zero

theorem tail_fS : Tail fS 0 3 := by
  refine ⟨Nat.zero_le _, fun j _ hj => ?_, rfl, fun i => ?_, by decide⟩
  · have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl | rfl <;> decide
  · simp only [fS]
    split
    · decide
    · split
      · decide
      · split <;> decide

def bwP : Block := Mem.empty.nextblock
def m0P : Mem := (Mem.alloc Mem.empty 0 24).1

def storesP : Option Mem := do
  let m ← Mem.store Mptr m0P bwP 0 nullV
  let m ← Mem.store Mptr m bwP 8 nullV
  Mem.store Mptr m bwP 16 nullV

theorem storesP_isSome : storesP.isSome = true := by decide

def mWP : Mem := storesP.get storesP_isSome

def cWP : Ctx where
  dataB := bwP
  dataO := Integers.Ptrofs.repr 0
  smbcB := bwP
  smbcO := Integers.Ptrofs.repr 8
  reqB := bwP
  reqO := Integers.Ptrofs.repr 16
  upV := nullV
  oldV := nullV
  reqV := nullV

theorem H0_cWP_satisfiable : ∃ hp, H0 cWP hp ∧ Heap.Agrees hp mWP := by
  obtain ⟨h1, m1, g1⟩ := cell (chunk := Mptr) (b := bwP) (ofs := 0) (v := nullV) (m := mWP)
    (by decide) (by decide)
  obtain ⟨h2, m2, g2⟩ := cell (chunk := Mptr) (b := bwP) (ofs := 8) (v := nullV) (m := mWP)
    (by decide) (by decide)
  obtain ⟨h3, m3, g3⟩ := cell (chunk := Mptr) (b := bwP) (ofs := 16) (v := nullV) (m := mWP)
    (by decide) (by decide)
  have d23 := mapsto_disj m2 m3 (by decide)
  have d1 : Heap.disjoint h1 (Heap.union h2 h3) :=
    Heap.disjoint_union_right.mpr ⟨mapsto_disj m1 m2 (by decide), mapsto_disj m1 m3 (by decide)⟩
  refine ⟨_, ?_, agrees_union g1 (agrees_union g2 g3)⟩
  have e0 : Integers.Ptrofs.unsigned cWP.dataO = 0 := by decide
  have e8 : Integers.Ptrofs.unsigned cWP.smbcO = 8 := by decide
  have e16 : Integers.Ptrofs.unsigned cWP.reqO = 16 := by decide
  refine ⟨h1, Heap.union h2 h3, d1, rfl, by unfold cD; rw [e0]; exact m1, h2, h3, d23, rfl,
    by unfold cS; rw [e8]; exact m2, Heap.emp, h3, Heap.disjoint_emp_left h3, (Heap.emp_union h3).symm,
    Or.inl ⟨rfl, rfl⟩, by unfold cR; rw [e16]; exact m3⟩

/-- **P0（C）: 修正前の関数には、`req->path` が `smbc->share` と同じブロックを指したまま CURLE_OK を返す入力がある。**

    `s/f` を share にすると、戻り値は CURLE_OK、`smbc->share = y.1 + 0`、`req->path = y.1 + 2`（`ppPostB` の `o'`、`k + 1 = 2`）。
    接続の破棄で `smbc->share`（ブロック `y.1`）が解放されると、`req->path` は解放済みのブロックを指す。 -/
theorem P0_C :
    ∃ (c : Ctx) (x y : PS) (k : Nat) (o : Integers.Ptrofs),
      (∃ hp m, H0 c hp ∧ Heap.Agrees hp m) ∧ IsPtr c.upV ∧ k < y.2.2
      ∧ Integers.Ptrofs.unsigned o = (k : _root_.Int) ∧ Tail y.2.1 0 y.2.2
      ∧ ∀ ge : CGenv, ge.genv_cenv = prog.prog_comp_env → ExtB ge x y o →
          ∀ vs, SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_smb_parse_url_path) (ppSpecB c y k) vs := by
  obtain ⟨hp, hH, hag⟩ := H0_cWP_satisfiable
  refine ⟨cWP, (bwP, fun _ => Integers.Int.zero, 0), (bwP, fS, 3), 1, Integers.Ptrofs.repr 1,
    ⟨hp, mWP, hH, hag⟩, Or.inr ⟨_, rfl⟩, by decide, by decide, tail_fS, ?_⟩
  intro ge hcenv X vs
  exact parse_before ge hcenv cWP _ _ 1 _ X (Or.inr ⟨_, rfl⟩) (by decide) (by decide) tail_fS vs

end Deb2026_3805B
