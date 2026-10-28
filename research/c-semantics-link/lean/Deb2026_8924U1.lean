/-
CVE-2026-8924（research/backport-proof-debian/cases/CVE-2026-8924.md）: 上流の修正後（U1、curl 51beed175d）の `is_public_suffix`。

証明すること（`ps_after`、P1）: `co->domain` の長さが `cl` で最後の文字が `.` のとき、`psl_is_cookie_domain_acceptable` を呼ぶ時点で
`lcookie` の `cl-1` 番目は 0。`psl_is_cookie_domain_acceptable` の仕様（`pslSpec`）の事前条件にこれを入れ、関数全体の三つ組を示す。
`domain` の最後の文字 `dch` は任意（`.` なら1つ取り除かれる）。`psl_is_cookie_domain_acceptable` の戻り値 `acc` も任意で、
戻り値は `acc` が 0 なら真（Cookie を捨てる）、そうでなければ偽。
-/
import GenDeb2026_8924U1
import Deb2026_8924Lib
import Case4debBefore
open CC CC.Sep CC.HProp
open Deb2026_8924_u1
open Deb2026_8924
open Deb2025_14524 (specK callK_none callS_some weaken pre_conv cell_valid boolVal_ptr cast_bool_ptr
  boolVal_ofBool_int)
open Case5C (addr RR return_const eval_field triple_nop_loop)
open Case4debC (lv_field eval_deref_temp)
open Case3C (CellD cellH Cells cell_load3 Locs)

set_option maxRecDepth 20000

namespace Deb2026_8924U

/-! ## 読むメモリ -/

structure Ctx where
  dB : Block                 -- data（NULL でない）
  dO : Integers.Ptrofs
  db : Integers.Int          -- その先頭のバイト（ポインタが有効であることを言うために所有する）
  coB : Block                -- co
  coO : Integers.Ptrofs
  mB : Block                 -- domain
  mO : Integers.Ptrofs
  mb0 : Integers.Int
  dl : Nat                   -- strlen(domain)
  dch : Integers.Int         -- domain[dl-1]
  kB : Block                 -- co->domain
  kO : Integers.Ptrofs
  kb0 : Integers.Int
  cl : Nat                   -- strlen(co->domain)。最後の文字は '.'
  pB : Block                 -- Curl_psl_use(data) が返すもの
  pO : Integers.Ptrofs
  pb : Integers.Int
  pm : Permission

def r64 (n : Nat) : Integers.Int64 := Integers.Int64.repr (n : _root_.Int)
def last (n : Nat) : Integers.Int64 :=
  Integers.Int64.sub (r64 n) (Integers.Int64.repr (Integers.Int.signed (Integers.Int.repr 1)))

abbrev outer (c : Ctx) : List CellD :=
  [(.Mint8unsigned, c.pm, c.dB, Integers.Ptrofs.unsigned c.dO, .Vint c.db),
   (Mptr, c.pm, c.coB, addr c.coO 8, .Vptr c.kB c.kO),
   (.Mint8unsigned, c.pm, c.mB, Integers.Ptrofs.unsigned c.mO, .Vint c.mb0),
   (.Mint8signed, c.pm, c.mB, Integers.Ptrofs.unsigned (lofs c.mO (last c.dl)), .Vint c.dch),
   (.Mint8unsigned, c.pm, c.kB, Integers.Ptrofs.unsigned c.kO, .Vint c.kb0),
   (.Mint8signed, c.pm, c.kB, Integers.Ptrofs.unsigned (lofs c.kO (last c.cl)), .Vint (Integers.Int.repr 46)),
   (.Mint8unsigned, c.pm, c.pB, Integers.Ptrofs.unsigned c.pO, .Vint c.pb)]

/-- 入口のメモリ（局所変数を除く）。 -/
def Hc (c : Ctx) : HProp := Cells (outer c)

def argsP (c : Ctx) : List Val := [.Vptr c.dB c.dO, .Vptr c.coB c.coO, .Vptr c.mB c.mO]

/-- `char` として読んだ値（証明の中で中身を展開しないように、既約にしておく）。 -/
@[irreducible] def ch8 (x : Integers.Int) : Integers.Int := Integers.Int.sign_ext 8 x

theorem ch8_eq (x : Integers.Int) : ch8 x = Integers.Int.sign_ext 8 x := by unfold ch8; rfl

/-- `domain` の最後の文字が `.` か。 -/
@[irreducible] def dq (c : Ctx) : Bool := Integers.Int.eq (ch8 c.dch) (Integers.Int.repr 46)

theorem dq_eq (c : Ctx) : dq c = Integers.Int.eq (ch8 c.dch) (Integers.Int.repr 46) := by unfold dq; rfl

/-- `domain` の末尾の `.` を取り除いたあとの長さ。 -/
def dl' (c : Ctx) : Nat := if dq c then c.dl - 1 else c.dl

/-- 局所変数の世界の形。 -/
def W0 (c : Ctx) (b1 b2 : Block) : HProp :=
  Hc c ∗ (anyBytes .Freeable b1 0 256 ∗ (anyBytes .Freeable b2 0 256 ∗ emp))
def W1 (c : Ctx) (b1 b2 : Block) : HProp :=
  Hc c ∗ (Arr3 b1 (dl' c) (.Vint (Integers.Int.repr 0)) ∗ (anyBytes .Freeable b2 0 256 ∗ emp))
/-- `psl_is_cookie_domain_acceptable` を呼ぶときの形: `lcookie` の `cl-1` 番目は `v`。 -/
def W2 (c : Ctx) (b1 b2 : Block) (v : Val) : HProp :=
  Hc c ∗ (Arr3 b1 (dl' c) (.Vint (Integers.Int.repr 0)) ∗ (Arr3 b2 (c.cl - 1) v ∗ emp))

/-- P1 の仕様: 戻り値は `acc` が 0 なら真。 -/
def psSpecA (c : Ctx) (acc : Integers.Int) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _Curl_easy noattr), tptr (Ty.Tstruct _Cookie noattr), tptr tschar]
  tyres := tbool
  cc := cc_default
  pre := fun vargs hp => vargs = argsP c ∧ Hc c hp
  post := fun v hp => v = Val.ofBool (Integers.Int.eq acc Integers.Int.zero) ∧ Hc c hp
  measure := fun _ => 0

/-- `strlen(p)` は `n` を返す。 -/
def strlenSpec (p : Val) (n : Nat) (K : HProp) : FunSpec where
  tyargs := [tptr tschar]
  tyres := tulong
  cc := cc_default
  pre := fun vargs hp => vargs = [p] ∧ K hp
  post := fun v hp => v = .Vlong (r64 n) ∧ K hp
  measure := fun _ => 0

/-- `psl_is_cookie_domain_acceptable(psl, lcase, lcookie)`: 呼ぶときのメモリが `K` であることを求め、`acc` を返す。 -/
def pslSpec (K : HProp) (acc : Integers.Int) : FunSpec where
  tyargs := [tptr (Ty.Tstruct _psl_ctx_st noattr), tptr tschar, tptr tschar]
  tyres := tint
  cc := cc_default
  pre := fun _ hp => K hp
  post := fun v hp => v = .Vint acc ∧ K hp
  measure := fun _ => 0

def sltTy : List Ty := [tptr tschar, tptr tschar, tulong]

structure Callee (ge : CGenv) (id : Ident) (fd : FunDef) where
  b : Block
  sym : Genv.findSymbol ge.genv_genv id = some b
  fp : FuncPtr ge b fd

/-- 呼ばれる側。局所変数のブロック `b1 b2` について全称。 -/
structure ExtP1 (ge : CGenv) (c : Ctx) (acc : Integers.Int) where
  fdS : FunDef
  sl : Callee ge _strlen fdS
  tS : typeOfFundef fdS = .Tfunction [tptr tschar] tulong cc_default
  sS1 : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdS (strlenSpec (.Vptr c.mB c.mO) c.dl (W0 c b1 b2)) vs
  sS2 : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdS (strlenSpec (.Vptr c.kB c.kO) c.cl (W0 c b1 b2)) vs
  fdI : FunDef
  ip : Callee ge _Curl_host_is_ipnum fdI
  tI : typeOfFundef fdI = .Tfunction [tptr tschar] tbool cc_default
  sI : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdI
    (specK [tptr tschar] tbool cc_default (W0 c b1 b2) (W0 c b1 b2) (some (Val.ofBool false))) vs
  fdU : FunDef
  pu : Callee ge _Curl_psl_use fdU
  tU : typeOfFundef fdU = .Tfunction [tptr (Ty.Tstruct _Curl_easy noattr)]
    (tptr (Ty.Tstruct _psl_ctx_st noattr)) cc_default
  sU : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdU
    (specK [tptr (Ty.Tstruct _Curl_easy noattr)] (tptr (Ty.Tstruct _psl_ctx_st noattr)) cc_default
      (W0 c b1 b2) (W0 c b1 b2) (some (.Vptr c.pB c.pO))) vs
  fdL : FunDef
  lw : Callee ge _Curl_strntolower fdL
  tL : typeOfFundef fdL = .Tfunction sltTy tvoid cc_default
  sL1 : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdL
    (specK sltTy tvoid cc_default (W0 c b1 b2) (W0 c b1 b2) none) vs
  sL2 : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdL
    (specK sltTy tvoid cc_default (W1 c b1 b2) (W1 c b1 b2) none) vs
  fdP : FunDef
  ps : Callee ge _psl_is_cookie_domain_acceptable fdP
  tP : typeOfFundef fdP = .Tfunction [tptr (Ty.Tstruct _psl_ctx_st noattr), tptr tschar, tptr tschar]
    tint cc_default
  sP : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdP
    (pslSpec (W2 c b1 b2 (.Vint (Integers.Int.repr 0))) acc) vs
  fdR : FunDef
  pr : Callee ge _Curl_psl_release fdR
  tR : typeOfFundef fdR = .Tfunction [tptr (Ty.Tstruct _Curl_easy noattr)] tvoid cc_default
  sR : ∀ b1 b2 vs, SatisfiesAt ge (FunctionEntry2 ge) fdR
    (specK [tptr (Ty.Tstruct _Curl_easy noattr)] tvoid cc_default
      (W2 c b1 b2 (.Vint (Integers.Int.repr 0))) (W2 c b1 b2 (.Vint (Integers.Int.repr 0))) none) vs

/-! ## 補題 -/

def coCk : Composite :=
  match prog.prog_comp_env.get _Cookie with
  | some co => co
  | none => { co_su := .Struct, co_members := [], co_attr := noattr,
              co_sizeof := 0, co_alignof := 1, co_rank := 0 }
theorem co_ck : prog.prog_comp_env.get _Cookie = some coCk := rfl
theorem off_dom : fieldOffset prog.prog_comp_env _domain coCk.co_members = .OK (8, .Full) := by decide

theorem ldC {l : List CellD} {R : HProp} {hp : Heap} {m : Mem} (hH : (Cells l ∗ R) hp)
    (hag : Heap.Agrees hp m) (k : Nat) (hk : k < l.length) {ch : Chunk} {p : Permission} {b : Block}
    {o : Z} {v : Val} (hl : l[k]'hk = (ch, p, b, o, v)) (hpr : permOrder p .Readable = true) :
    Mem.load ch m b o = some (Val.loadResult ch v) :=
  cell_load3 hl hpr hH hag

theorem validC {l : List CellD} {R : HProp} {hp : Heap} {m : Mem} (hH : (Cells l ∗ R) hp)
    (hag : Heap.Agrees hp m) (k : Nat) (hk : k < l.length) {p : Permission} {b : Block}
    {o : Integers.Ptrofs} {v : Val}
    (hl : l[k]'hk = (.Mint8unsigned, p, b, Integers.Ptrofs.unsigned o, v))
    (hpn : permOrder p .Nonempty = true) :
    Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true :=
  cell_valid hl hpn hH hag

theorem boolVal_ptrT {b : Block} {o : Integers.Ptrofs} {m : Mem} (t : Ty)
    (hv : Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true) :
    Cop.boolVal (.Vptr b o) (tptr t) m = some true := by
  simp only [Cop.boolVal, hv]
  rfl

theorem last_eq (n : Nat) (h : 1 ≤ n) : last n = r64 (n - 1) := by
  unfold last r64
  rw [show Integers.Int.signed (Integers.Int.repr 1) = ((1 : Nat) : _root_.Int) by decide]
  exact u64_sub n 1 h

theorem r64_nz (n : Nat) (h1 : 1 ≤ n) (h2 : n < 18446744073709551616) :
    Integers.Int64.eq (r64 n) Integers.Int64.zero = false := by
  have := u64_eq n 0 (by omega) (by omega)
  unfold r64
  rw [show Integers.Int64.zero = Integers.Int64.repr ((0 : Nat) : _root_.Int) from rfl, this]
  simp; omega

theorem lt256 (n : Nat) (h : n < 256) :
    Integers.Int64.cmpu .Clt (r64 n) (Integers.Int64.repr 256) = true := by
  have := cmpu_lt_nat n 256 (by omega) (by omega)
  unfold r64
  rw [show Integers.Int64.repr 256 = Integers.Int64.repr ((256 : Nat) : _root_.Int) from rfl, this]
  simp; omega

theorem cast_ofBool_bool (b : Bool) (m : Mem) :
    Cop.semCast (Val.ofBool b) tint tbool m = some (Val.ofBool b) := by cases b <;> rfl

theorem notbool_ofBool (b : Bool) (m : Mem) :
    Cop.semUnaryOperation .Onotbool (Val.ofBool b) tbool m = some (Val.ofBool (!b)) := by cases b <;> rfl

theorem semEq_char (cenv : CompositeEnv) (m : Mem) (x : Integers.Int) :
    Cop.semBinaryOperation cenv .Oeq (.Vint x) tschar (.Vint (Integers.Int.repr 46)) tint m
      = some (Val.ofBool (Integers.Int.eq x (Integers.Int.repr 46))) := by
  show some (Val.ofBool (Integers.Int.cmp .Ceq x (Integers.Int.repr 46))) = _
  rfl

theorem ltS (cenv : CompositeEnv) (m : Mem) (n : Nat) (h : n < 256) :
    Cop.semBinaryOperation cenv .Olt (.Vlong (r64 n)) tulong
      (.Vlong (Integers.Int64.repr (sizeof cenv (tarray tschar 256)))) tulong m = some (Val.ofBool true) := by
  show some (Val.ofBool (Integers.Int64.cmpu .Clt (r64 n) (Integers.Int64.repr 256))) = _
  rw [lt256 n h]

theorem cast_int_bool (x : Integers.Int) (m : Mem) :
    Cop.semCast (.Vint x) tint tbool m = some (Val.ofBool (!Integers.Int.eq x Integers.Int.zero)) := by
  show some (Val.Vint (if Integers.Int.eq x Integers.Int.zero then Integers.Int.zero else Integers.Int.one)) = _
  cases Integers.Int.eq x Integers.Int.zero <;> rfl

theorem boolVal_long (x : Integers.Int64) (m : Mem) :
    Cop.boolVal (.Vlong x) tulong m = some (!Integers.Int64.eq x Integers.Int64.zero) := rfl

def envP (b1 b2 : Block) : Env :=
  (emptyEnv.set _lcase (b1, tarray tschar 256)).set _lcookie (b2, tarray tschar 256)

abbrev lP (c : Ctx) : List (Ident × Val) :=
  [(_domain, .Vptr c.mB c.mO), (_co, .Vptr c.coB c.coO), (_data, .Vptr c.dB c.dO)]

def PbodyP (c : Ctx) : Sep.Assn := fun e le hp =>
  ∃ bs : Block × Block, bs.1 ≠ bs.2 ∧
    LocalSt (envP bs.1 bs.2) (lP c) (W0 c bs.1 bs.2) e le hp

theorem blocks_envP (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env) (b1 b2 : Block) :
    blocksOfEnv ge.genv_cenv (envP b1 b2) = [(b1, 0, 256), (b2, 0, 256)] := by
  rw [hcenv]; rfl

macro "envgetP" : tactic =>
  `(tactic| (unfold envP; repeat (first
      | exact PTree.gss _ _ _
      | exact PTree.gempty _
      | refine (PTree.gso _ _ _ _ (by decide)).trans ?_)))

/-- 配列の変数 `x`（`char x[256]`）の値（先頭のポインタ）。 -/
theorem eval_arr {ge : CGenv} {e : Env} {le : TempEnv} {m : Mem} {x : Ident} {b : Block}
    (he : e.get x = some (b, tarray tschar 256)) :
    EvalExpr ge e le m (.Evar x (tarray tschar 256)) (.Vptr b Integers.Ptrofs.zero) :=
  EvalExpr.Elvalue _ _ _ .Full _ (EvalLvalue.Evar_local _ _ _ he) (DerefLoc.reference rfl)

theorem W2_ret {c : Ctx} {b1 b2 : Block} {v : Val} {hp : Heap} (hdl : dl' c < 256) (hcl : c.cl - 1 < 256)
    (h : W2 c b1 b2 v hp) : (Hc c ∗ Locs [(b1, 256), (b2, 256)]) hp := by
  obtain ⟨h1, h2, d, rfl, hc, h3, h4, d2, rfl, a3, h5, h6, d3, rfl, a5, he⟩ := h
  exact ⟨h1, _, d, rfl, hc, h3, _, d2, rfl, arr_join hdl a3, h5, h6, d3, rfl, arr_join hcl a5, he⟩

/-! ## 本体 -/

set_option maxHeartbeats 40000000 in
theorem ps_body_after (ge : CGenv) (c : Ctx) (acc : Integers.Int)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hdl1 : 2 ≤ c.dl) (hdl2 : c.dl < 256) (hcl1 : 2 ≤ c.cl) (hcl2 : c.cl ≤ 256)
    (X : ExtP1 ge c acc) :
    Triple ge (FunctionEntry2 ge) f_is_public_suffix (PbodyP c) f_is_public_suffix.fn_body
      (RR (psSpecA c acc).post Sep.Assn.no) := by
  refine Sep.triple_exists ge _ _ _ _ _ (fun bs => ?_)
  obtain ⟨b1, b2⟩ := bs
  refine Case1C.triple_pure ge _ _ _ _ _ _ (fun hne => ?_)
  change Triple _ _ _ (LocalSt (envP b1 b2) (lP c) (W0 c b1 b2)) _ _
  have hdl' : dl' c < 256 := by unfold dl'; split <;> omega
  have hcl' : c.cl - 1 < 256 := by omega
  -- DEBUGF(…)
  refine triple_seq_fwd ge _ _ _ _ _ _ _ (triple_nop_loop ge _ _ _) ?_
  refine triple_seq ge _ _ _ (fun e le hp => Integers.Int.eq acc Integers.Int.zero = false ∧
      LocalSt (envP b1 b2) [] (Hc c ∗ Locs [(b1, 256), (b2, 256)]) e le hp) _ _ _ ?main ?ret
  case ret =>
    refine Case4debC.triple_pure_pre ge _ _ _ _ _ _ (fun hφ => ?_)
    refine Case3C.ret_locs ge _ _ (envP b1 b2) _ (Hc c) [(b1, 256), (b2, 256)] _
      (.Vint (Integers.Int.repr 0)) (Val.ofBool false) _ (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)
      (fun _ => rfl) ?_ ?_ (fun hp hH => ⟨by rw [hφ], hH⟩)
    · rw [blocks_envP ge hcenv]
      intro x hx'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'
      rcases hx' with rfl | rfl
      · exact ⟨b1, 256, rfl, by simp⟩
      · exact ⟨b2, 256, rfl, by simp⟩
    · rw [blocks_envP ge hcenv]
      simp [hne]
  case main =>
  -- if(data && (domain && co->domain && !Curl_host_is_ipnum(co->domain)))
  refine triple_seq_fwd ge _ _ _ ?Q1 _ _ _ ?a1 ?a2
  case a1 =>
    refine triple_if_local ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ true _ _ _
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ (.Vptr c.dB c.dO) (hT.get (by temps_get)),
        boolVal_ptrT _ (validC hH hag 0 (by simp) rfl hpn)⟩) ?_
    rw [if_pos rfl]
    refine triple_seq_fwd ge _ _ _ ?Q2 _ _ _ ?c1 ?c2
    case c1 =>
      refine triple_if_local ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ true _ _ _
        (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ (.Vptr c.mB c.mO) (hT.get (by temps_get)),
          boolVal_ptrT _ (validC hH hag 2 (by simp) rfl hpn)⟩) ?_
      rw [if_pos rfl]
      refine triple_seq_fwd ge _ _ _ ?Q3 _ _ _ ?d1 ?d2
      case d1 =>
        refine triple_set_local_fwd ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ _ (.Vptr c.kB c.kO) ?_
        intro le m hp hT hH hag
        exact eval_field (hT.get (by temps_get)) (hcenv ▸ co_ck) (hcenv ▸ off_dom) rfl
          (ldC hH hag 1 (by simp) rfl hpr)
      case d2 =>
        refine triple_set_local_fwd ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ _ (Val.ofBool true) ?_
        intro le m hp hT hH hag
        exact EvalExpr.Ecast _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vptr c.kB c.kO) (hT.get (by temps_get)))
          (cast_bool_ptr (validC hH hag 4 (by simp) rfl hpn))
    case c2 =>
      refine triple_if_local ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ true _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool true) (hT.get (by temps_get)), rfl⟩) ?_
      rw [if_pos rfl]
      refine triple_seq_fwd ge _ _ _ ?Q4 _ _ _ ?e1 ?e2
      case e1 =>
        refine triple_seq_fwd ge _ _ _ ?Q5 _ _ _ ?f1 ?f2
        case f1 =>
          refine triple_seq_fwd ge _ _ _ ?Q6 _ _ _ ?g1 ?g2
          case g1 =>
            refine triple_set_local_fwd ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ _ (.Vptr c.kB c.kO) ?_
            intro le m hp hT hH hag
            exact eval_field (hT.get (by temps_get)) (hcenv ▸ co_ck) (hcenv ▸ off_dom) rfl
              (ldC hH hag 1 (by simp) rfl hpr)
          case g2 =>
            refine callS_some ge _ _ _ (W0 c b1 b2) (W0 c b1 b2) (Val.ofBool false) _ _ _ (envP b1 b2) _
              [.Vptr c.kB c.kO] X.ip.b X.fdI (X.sI b1 b2) X.ip.fp X.tI ?_ ?_ ?_
              (fun hp hK => hK) (fun v hp h => ⟨h.1 _ rfl, h.2⟩)
            · rfl
            · intro _ _ _; exact eval_callee_global (by envgetP) X.ip.sym rfl
            intro le m hT
            exact EvalExprlist.cons _ _ _ _ _ _ _
              (EvalExpr.Etempvar _ _ (.Vptr c.kB c.kO) (hT.get (by temps_get))) rfl EvalExprlist.nil
        case f2 =>
          refine triple_set_local_fwd ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ _ (Val.ofBool true) ?_
          intro le m hp hT _ _
          exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Eunop _ _ _ _ _
            (EvalExpr.Etempvar _ _ (Val.ofBool false) (hT.get (by temps_get))) rfl) rfl
      case e2 =>
        refine triple_set_local_fwd ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ _ (Val.ofBool true) ?_
        intro le m hp hT _ _
        exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ (Val.ofBool true) (hT.get (by temps_get))) rfl
  case a2 =>
  refine triple_if_local ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ true _ _ _
    (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool true) (hT.get (by temps_get)), rfl⟩) ?_
  rw [if_pos rfl]
  -- acceptable = FALSE; dlen = strlen(domain); clen = strlen(co->domain);
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ _ (Val.ofBool false)
      (fun _ _ _ _ _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (callS_some ge _ _ _ (W0 c b1 b2) (W0 c b1 b2) (.Vlong (r64 c.dl)) _ _ _ (envP b1 b2) _
        [.Vptr c.mB c.mO] X.sl.b X.fdS (X.sS1 b1 b2) X.sl.fp X.tS rfl
        (fun _ _ _ => eval_callee_global (by envgetP) X.sl.sym rfl)
        (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vptr c.mB c.mO) (hT.get (by temps_get))) rfl EvalExprlist.nil)
        (fun hp hK => ⟨rfl, hK⟩) (fun v hp h => h))
      (triple_set_local_fwd ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ _ (.Vlong (r64 c.dl))
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ _ (.Vptr c.kB c.kO)
          (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_ck) (hcenv ▸ off_dom) rfl (ldC hH hag 1 (by simp) rfl hpr)))
        (callS_some ge _ _ _ (W0 c b1 b2) (W0 c b1 b2) (.Vlong (r64 c.cl)) _ _ _ (envP b1 b2) _
          [.Vptr c.kB c.kO] X.sl.b X.fdS (X.sS2 b1 b2) X.sl.fp X.tS rfl
          (fun _ _ _ => eval_callee_global (by envgetP) X.sl.sym rfl)
          (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ (.Vptr c.kB c.kO) (hT.get (by temps_get))) rfl EvalExprlist.nil)
          (fun hp hK => ⟨rfl, hK⟩) (fun v hp h => h)))
      (triple_set_local_fwd ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ _ (.Vlong (r64 c.cl))
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))) ?_
  -- if(dlen && (domain[dlen - 1] == '.')) dlen--;
  refine triple_seq_fwd ge _ _ _ (LocalSt (envP b1 b2)
    [(_dlen, .Vlong (r64 (dl' c))), (_clen, .Vlong (r64 c.cl)), (_acceptable, Val.ofBool false),
     (_domain, .Vptr c.mB c.mO), (_co, .Vptr c.coB c.coO), (_data, .Vptr c.dB c.dO)] (W0 c b1 b2))
    _ _ _ ?dt ?r1
  case dt =>
    refine triple_seq_fwd ge _ _ _ ?Qd _ _ _ ?x1 ?x2
    case x1 =>
      refine triple_if_local ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ true _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (.Vlong (r64 c.dl)) (hT.get (by temps_get)),
          (boolVal_long _ m).trans (by rw [r64_nz c.dl (by omega) (by omega)]; rfl)⟩) ?_
      rw [if_pos rfl]
      refine triple_seq_fwd ge _ _ _ ?Qd1 _ _ _ ?y1 ?y2
      case y1 =>
        refine triple_set_local_fwd ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ _
          (.Vint (ch8 c.dch)) ?_
        intro le m hp hT hH hag
        rw [ch8_eq]
        exact EvalExpr.Elvalue _ _ _ .Full _
          (EvalLvalue.Ederef _ _ _ _
            (EvalExpr.Ebinop _ _ _ _ _ _ _
              (EvalExpr.Etempvar _ _ (.Vptr c.mB c.mO) (hT.get (by temps_get)))
              (EvalExpr.Ebinop _ _ _ _ _ _ _
                (EvalExpr.Etempvar _ _ (.Vlong (r64 c.dl)) (hT.get (by temps_get)))
                (EvalExpr.Econst_int _ _) (semBinop_sub_ulong_int _ _ _ _))
              (semAdd_long _ _ _ _ _ _ (Or.inl rfl))))
          (DerefLoc.value .Mint8signed _ rfl (ldC hH hag 3 (by simp) rfl hpr))
      case y2 =>
        refine triple_set_local_fwd ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ _ (Val.ofBool (dq c)) ?_
        intro le m hp hT _ _
        exact EvalExpr.Ecast _ _ (Val.ofBool (dq c)) _
          (EvalExpr.Ebinop _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ (.Vint (ch8 c.dch)) (hT.get (by temps_get)))
            (EvalExpr.Econst_int _ _) ((semEq_char _ _ _).trans (by rw [dq_eq])))
          (cast_ofBool_bool _ m)
    case x2 =>
      rcases Bool.eq_false_or_eq_true (dq c) with hb | hb
      · have hd : dl' c = c.dl - 1 := by unfold dl'; rw [hb]; rfl
        rw [hd]
        refine triple_if_local ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ true _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _
            (Val.ofBool (dq c)) (hT.get (by temps_get)), (boolVal_ofBool_int _ m).trans (by rw [hb])⟩) ?_
        rw [if_pos rfl]
        refine weaken ge _ _ (triple_set_local_fwd ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ _
          (.Vlong (r64 (c.dl - 1))) ?_) (by subt)
        intro le m hp hT _ _
        rw [← last_eq c.dl (by omega)]
        exact EvalExpr.Ebinop _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vlong (r64 c.dl)) (hT.get (by temps_get)))
          (EvalExpr.Econst_int _ _) (semBinop_sub_ulong_int _ _ _ _)
      · have hd : dl' c = c.dl := by unfold dl'; rw [hb]; rfl
        rw [hd]
        refine triple_if_local ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ false _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _
            (Val.ofBool (dq c)) (hT.get (by temps_get)), (boolVal_ofBool_int _ m).trans (by rw [hb])⟩) ?_
        rw [if_neg Bool.false_ne_true]
        exact weaken ge _ _ (triple_skip ge _ _ _) (by subt)
  case r1 =>
  -- if(clen && (co->domain[clen - 1] == '.')) clen--;
  refine triple_seq_fwd ge _ _ _ (LocalSt (envP b1 b2)
    [(_clen, .Vlong (r64 (c.cl - 1))), (_dlen, .Vlong (r64 (dl' c))), (_acceptable, Val.ofBool false),
     (_domain, .Vptr c.mB c.mO), (_co, .Vptr c.coB c.coO), (_data, .Vptr c.dB c.dO)] (W0 c b1 b2))
    _ _ _ ?ct ?r2
  case ct =>
    refine triple_seq_fwd ge _ _ _ ?Qc _ _ _ ?x1 ?x2
    case x1 =>
      refine triple_if_local ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ true _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (.Vlong (r64 c.cl)) (hT.get (by temps_get)),
          (boolVal_long _ m).trans (by rw [r64_nz c.cl (by omega) (by omega)]; rfl)⟩) ?_
      rw [if_pos rfl]
      refine triple_seq_fwd ge _ _ _ ?Qc1 _ _ _ ?y1 ?y2
      case y1 =>
        refine triple_set_local_fwd ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ _ (.Vptr c.kB c.kO) ?_
        intro le m hp hT hH hag
        exact eval_field (hT.get (by temps_get)) (hcenv ▸ co_ck) (hcenv ▸ off_dom) rfl
          (ldC hH hag 1 (by simp) rfl hpr)
      case y2 =>
      refine triple_seq_fwd ge _ _ _ ?Qc2 _ _ _ ?z1 ?z2
      case z1 =>
        refine triple_set_local_fwd ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ _
          (.Vint (ch8 (Integers.Int.repr 46))) ?_
        intro le m hp hT hH hag
        rw [ch8_eq]
        exact EvalExpr.Elvalue _ _ _ .Full _
          (EvalLvalue.Ederef _ _ _ _
            (EvalExpr.Ebinop _ _ _ _ _ _ _
              (EvalExpr.Etempvar _ _ (.Vptr c.kB c.kO) (hT.get (by temps_get)))
              (EvalExpr.Ebinop _ _ _ _ _ _ _
                (EvalExpr.Etempvar _ _ (.Vlong (r64 c.cl)) (hT.get (by temps_get)))
                (EvalExpr.Econst_int _ _) (semBinop_sub_ulong_int _ _ _ _))
              (semAdd_long _ _ _ _ _ _ (Or.inl rfl))))
          (DerefLoc.value .Mint8signed _ rfl (ldC hH hag 5 (by simp) rfl hpr))
      case z2 =>
        refine triple_set_local_fwd ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ _ (Val.ofBool true) ?_
        intro le m hp hT _ _
        exact EvalExpr.Ecast _ _ (Val.ofBool true) _
          (EvalExpr.Ebinop _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ (.Vint (ch8 (Integers.Int.repr 46))) (hT.get (by temps_get)))
            (EvalExpr.Econst_int _ _)
            ((semEq_char _ _ _).trans (by rw [ch8_eq]; rfl))) (cast_ofBool_bool _ m)
    case x2 =>
      refine triple_if_local ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ true _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool true) (hT.get (by temps_get)), rfl⟩) ?_
      rw [if_pos rfl]
      refine weaken ge _ _ (triple_set_local_fwd ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ _
        (.Vlong (r64 (c.cl - 1))) ?_) (by subt)
      intro le m hp hT _ _
      rw [← last_eq c.cl (by omega)]
      exact EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ (.Vlong (r64 c.cl)) (hT.get (by temps_get)))
        (EvalExpr.Econst_int _ _) (semBinop_sub_ulong_int _ _ _ _)
  case r2 =>
  -- if((dlen < sizeof(lcase)) && (clen < sizeof(lcookie))) { psl = Curl_psl_use(data); if(psl) { … } }
  refine triple_seq_fwd ge _ _ _ (LocalSt (envP b1 b2)
    [(_acceptable, Val.ofBool (!Integers.Int.eq acc Integers.Int.zero))]
    (W2 c b1 b2 (.Vint (Integers.Int.repr 0)))) _ _ _ ?sz ?fin
  case sz =>
    refine triple_seq_fwd ge _ _ _ ?Qs _ _ _ ?s1 ?s2
    case s1 =>
      refine triple_if_local ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ true _ _ _
        (fun le m hp hT _ _ => ⟨Val.ofBool true, EvalExpr.Ebinop _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vlong (r64 (dl' c))) (hT.get (by temps_get)))
          (EvalExpr.Esizeof _ _) (ltS _ _ _ hdl'), rfl⟩) ?_
      rw [if_pos rfl]
      refine triple_set_local_fwd ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ _ (Val.ofBool true) ?_
      intro le m hp hT _ _
      exact EvalExpr.Ecast _ _ (Val.ofBool true) _ (EvalExpr.Ebinop _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vlong (r64 (c.cl - 1))) (hT.get (by temps_get)))
          (EvalExpr.Esizeof _ _) (ltS _ _ _ hcl')) rfl
    case s2 =>
    refine triple_if_local ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ true _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool true) (hT.get (by temps_get)), rfl⟩) ?_
    rw [if_pos rfl]
    refine triple_seq_fwd ge _ _ _ ?Qp _ _ _ ?p1 ?p2
    case p1 =>
      refine triple_seq_fwd ge _ _ _ ?Qp1 _ _ _ ?q1 ?q2
      case q1 =>
        refine callS_some ge _ _ _ (W0 c b1 b2) (W0 c b1 b2) (.Vptr c.pB c.pO) _ _ _ (envP b1 b2) _
          [.Vptr c.dB c.dO] X.pu.b X.fdU (X.sU b1 b2) X.pu.fp X.tU ?_ ?_ ?_
          (fun hp hK => hK) (fun v hp h => ⟨h.1 _ rfl, h.2⟩)
        · rfl
        · intro _ _ _; exact eval_callee_global (by envgetP) X.pu.sym rfl
        intro le m hT
        exact EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vptr c.dB c.dO) (hT.get (by temps_get))) rfl EvalExprlist.nil
      case q2 =>
        refine triple_set_local_fwd ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ _ (.Vptr c.pB c.pO) ?_
        intro le m hp hT _ _
        exact EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))
    case p2 =>
    refine triple_if_local ge _ _ (envP b1 b2) _ (W0 c b1 b2) _ true _ _ _
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ (.Vptr c.pB c.pO) (hT.get (by temps_get)),
        boolVal_ptrT _ (validC hH hag 6 (by simp) rfl hpn)⟩) ?_
    rw [if_pos rfl]
    -- Curl_strntolower(lcase, domain, dlen); lcase[dlen] = 0;
    refine triple_seq_fwd ge _ _ _ ?Qi1 _ _ _ ?i1 ?i2
    case i1 =>
      refine callK_none ge _ _ sltTy tvoid cc_default (W0 c b1 b2) (W0 c b1 b2) none _ _ (envP b1 b2) _
        [.Vptr b1 Integers.Ptrofs.zero, .Vptr c.mB c.mO, .Vlong (r64 (dl' c))]
        X.lw.b X.fdL (X.sL1 b1 b2) X.lw.fp X.tL ?_ ?_ ?_
      · rfl
      · intro _ _ _; exact eval_callee_global (by envgetP) X.lw.sym rfl
      intro le m hT
      exact EvalExprlist.cons _ _ _ _ _ _ _ (eval_arr (by envgetP)) rfl
        (EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vptr c.mB c.mO) (hT.get (by temps_get))) rfl
          (EvalExprlist.cons _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ (.Vlong (r64 (dl' c))) (hT.get (by temps_get))) rfl EvalExprlist.nil))
    case i2 =>
    refine triple_seq_fwd ge _ _ _ ?Qi2 _ _ _ ?j1 ?j2
    case j1 =>
      refine store_arr ge _ _ (envP b1 b2) _ (Hc c) (anyBytes .Freeable b2 0 256 ∗ emp) b1
        (lofs Integers.Ptrofs.zero (r64 (dl' c))) (dl' c) hdl' (lofs_zero_unsigned _ hdl')
        (.Vint (Integers.Int.repr 0)) _ _ ?_ ?_ ?_
      · rfl
      · intro le m hT
        exact EvalLvalue.Ederef _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _ (eval_arr (by envgetP))
          (EvalExpr.Etempvar _ _ (.Vlong (r64 (dl' c))) (hT.get (by temps_get)))
          (semAdd_long _ _ _ _ _ _ (Or.inr rfl)))
      · intro le m hT
        exact ⟨_, EvalExpr.Econst_int _ _, rfl⟩
    case j2 =>
    refine pre_conv ge _ _ (H2 := W1 c b1 b2) (fun hp h => h) ?_
    -- Curl_strntolower(lcookie, co->domain, clen); lcookie[clen] = 0;
    refine triple_seq_fwd ge _ _ _ ?Qk1 _ _ _ ?k1 ?k2
    case k1 =>
      refine triple_seq_fwd ge _ _ _ ?Qk2 _ _ _ ?l1 ?l2
      case l1 =>
        refine triple_set_local_fwd ge _ _ (envP b1 b2) _ (W1 c b1 b2) _ _ (.Vptr c.kB c.kO) ?_
        intro le m hp hT hH hag
        exact eval_field (hT.get (by temps_get)) (hcenv ▸ co_ck) (hcenv ▸ off_dom) rfl
          (ldC hH hag 1 (by simp) rfl hpr)
      case l2 =>
        refine callK_none ge _ _ sltTy tvoid cc_default (W1 c b1 b2) (W1 c b1 b2) none _ _ (envP b1 b2) _
          [.Vptr b2 Integers.Ptrofs.zero, .Vptr c.kB c.kO, .Vlong (r64 (c.cl - 1))]
          X.lw.b X.fdL (X.sL2 b1 b2) X.lw.fp X.tL ?_ ?_ ?_
        · rfl
        · intro _ _ _; exact eval_callee_global (by envgetP) X.lw.sym rfl
        intro le m hT
        exact EvalExprlist.cons _ _ _ _ _ _ _ (eval_arr (by envgetP)) rfl
          (EvalExprlist.cons _ _ _ _ _ _ _
            (EvalExpr.Etempvar _ _ (.Vptr c.kB c.kO) (hT.get (by temps_get))) rfl
            (EvalExprlist.cons _ _ _ _ _ _ _
              (EvalExpr.Etempvar _ _ (.Vlong (r64 (c.cl - 1))) (hT.get (by temps_get))) rfl EvalExprlist.nil))
    case k2 =>
    refine triple_seq_fwd ge _ _ _ ?Qk3 _ _ _ ?m1 ?m2
    case m1 =>
      refine pre_conv ge _ _ (H2 := (Hc c ∗ Arr3 b1 (dl' c) (.Vint (Integers.Int.repr 0)))
        ∗ (anyBytes .Freeable b2 0 256 ∗ emp)) (fun hp h => by unfold W1 at h; rwa [← sep_assoc_eq] at h) ?_
      refine store_arr ge _ _ (envP b1 b2) _ _ emp b2
        (lofs Integers.Ptrofs.zero (r64 (c.cl - 1))) (c.cl - 1) hcl' (lofs_zero_unsigned _ hcl')
        (.Vint (Integers.Int.repr 0)) _ _ ?_ ?_ ?_
      · rfl
      · intro le m hT
        exact EvalLvalue.Ederef _ _ _ _ (EvalExpr.Ebinop _ _ _ _ _ _ _ (eval_arr (by envgetP))
          (EvalExpr.Etempvar _ _ (.Vlong (r64 (c.cl - 1))) (hT.get (by temps_get)))
          (semAdd_long _ _ _ _ _ _ (Or.inr rfl)))
      · intro le m hT
        exact ⟨_, EvalExpr.Econst_int _ _, rfl⟩
    case m2 =>
    refine pre_conv ge _ _ (H2 := W2 c b1 b2 (.Vint (Integers.Int.repr 0)))
      (fun hp h => by unfold W2; rwa [sep_assoc_eq] at h) ?_
    -- acceptable = psl_is_cookie_domain_acceptable(psl, lcase, lcookie); Curl_psl_release(data);
    refine triple_seq_fwd ge _ _ _ ?Qn1 _ _ _ ?n1 ?n2
    case n1 =>
      refine triple_seq_fwd ge _ _ _ ?Qn2 _ _ _ ?o1 ?o2
      case o1 =>
        refine callS_some ge _ _ _ (W2 c b1 b2 (.Vint (Integers.Int.repr 0)))
          (W2 c b1 b2 (.Vint (Integers.Int.repr 0))) (.Vint acc) _ _ _ (envP b1 b2) _
          [.Vptr c.pB c.pO, .Vptr b1 Integers.Ptrofs.zero, .Vptr b2 Integers.Ptrofs.zero]
          X.ps.b X.fdP (X.sP b1 b2) X.ps.fp X.tP ?_ ?_ ?_ (fun hp hK => hK) (fun v hp h => h)
        · rfl
        · intro _ _ _; exact eval_callee_global (by envgetP) X.ps.sym rfl
        intro le m hT
        exact EvalExprlist.cons _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vptr c.pB c.pO) (hT.get (by temps_get))) rfl
          (EvalExprlist.cons _ _ _ _ _ _ _ (eval_arr (by envgetP)) rfl
            (EvalExprlist.cons _ _ _ _ _ _ _ (eval_arr (by envgetP)) rfl EvalExprlist.nil))
      case o2 =>
        refine triple_set_local_fwd ge _ _ (envP b1 b2) _ (W2 c b1 b2 (.Vint (Integers.Int.repr 0))) _ _
          (Val.ofBool (!Integers.Int.eq acc Integers.Int.zero)) ?_
        intro le m hp hT _ _
        exact EvalExpr.Ecast _ _ _ _ (EvalExpr.Etempvar _ _ (.Vint acc) (hT.get (by temps_get)))
          (cast_int_bool _ m)
    case n2 =>
      refine weaken ge _ _ (callK_none ge _ _ [tptr (Ty.Tstruct _Curl_easy noattr)] tvoid cc_default
        (W2 c b1 b2 (.Vint (Integers.Int.repr 0))) (W2 c b1 b2 (.Vint (Integers.Int.repr 0))) none _ _
        (envP b1 b2) _ [.Vptr c.dB c.dO] X.pr.b X.fdR (X.sR b1 b2) X.pr.fp X.tR ?_ ?_ ?_) (by subt)
      · rfl
      · intro _ _ _; exact eval_callee_global (by envgetP) X.pr.sym rfl
      intro le m hT
      exact EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ (.Vptr c.dB c.dO) (hT.get (by temps_get))) rfl EvalExprlist.nil
  case fin =>
  -- if(!acceptable) return TRUE;
  rcases Bool.eq_false_or_eq_true (Integers.Int.eq acc Integers.Int.zero) with ha | ha
  · refine triple_if_local ge _ _ (envP b1 b2) _ (W2 c b1 b2 (.Vint (Integers.Int.repr 0))) _ true _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
        (EvalExpr.Etempvar _ _ (Val.ofBool (!Integers.Int.eq acc Integers.Int.zero)) (hT.get (by temps_get)))
        (notbool_ofBool _ m),
        (boolVal_ofBool_int _ m).trans (by rw [ha]; rfl)⟩) ?_
    rw [if_pos rfl]
    refine triple_seq ge _ _ _ _ _ _ _ (Sep.triple_fallthrough ge _ _ _ _ _ _ (triple_nop_loop ge _ _ _)
      (fun _ _ _ x => x)) ?_
    refine pre_conv ge _ _ (fun _ h => W2_ret hdl' hcl' h) ?_
    refine Sep.triple_conseq (R := RR (psSpecA c acc).post Sep.Assn.no) ge _ _ ?_ (fun _ _ _ x => x) (fun _ _ _ x => False.elim x)
      (fun _ _ _ x => x) (fun _ _ _ x => x) (fun _ _ x => x)
    refine Case3C.ret_locs ge _ _ (envP b1 b2) _ (Hc c) [(b1, 256), (b2, 256)] _
      (.Vint (Integers.Int.repr 1)) (Val.ofBool true) _ (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)
      ?_ ?_ ?_ ?_
    · intro _; rfl
    · rw [blocks_envP ge hcenv]
      intro x hx'
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'
      rcases hx' with rfl | rfl
      · exact ⟨b1, 256, rfl, by simp⟩
      · exact ⟨b2, 256, rfl, by simp⟩
    · rw [blocks_envP ge hcenv]
      simp [hne]
    · intro hp hH; exact ⟨by rw [ha], hH⟩
  · refine triple_if_local ge _ _ (envP b1 b2) _ (W2 c b1 b2 (.Vint (Integers.Int.repr 0))) _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
        (EvalExpr.Etempvar _ _ (Val.ofBool (!Integers.Int.eq acc Integers.Int.zero)) (hT.get (by temps_get)))
        (notbool_ofBool _ m),
        (boolVal_ofBool_int _ m).trans (by rw [ha]; rfl)⟩) ?_
    rw [if_neg Bool.false_ne_true]
    exact triple_conseq ge _ _ (triple_skip ge _ _ _) (fun _ _ _ x => x)
      (fun _ _ _ ⟨he, _, hW⟩ => ⟨ha, he, TempsHold_nil _, W2_ret hdl' hcl' hW⟩)
      (fun _ _ _ x => x.elim) (fun _ _ _ x => x.elim) (fun _ _ x => x.elim)

/-! ## 関数全体 -/

/-- **P1（U1）**: 修正後の `is_public_suffix` は、`lcookie` の `cl-1` 番目を 0 にしてから PSL の検査に渡す。 -/
theorem ps_after (ge : CGenv) (c : Ctx) (acc : Integers.Int)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hdl1 : 2 ≤ c.dl) (hdl2 : c.dl < 256) (hcl1 : 2 ≤ c.cl) (hcl2 : c.cl ≤ 256)
    (X : ExtP1 ge c acc) (vs : List Val) :
    SatisfiesAt ge (FunctionEntry2 ge) (.Internal f_is_public_suffix) (psSpecA c acc) vs := by
  by_cases hvs : vs = argsP c
  case neg =>
    intro k m hp hf _ hpre
    exact absurd hpre.1 hvs
  subst hvs
  have hnv : listNorepet (varNames f_is_public_suffix.fn_vars) := by decide
  have hnp : listNorepet (varNames f_is_public_suffix.fn_params) := by decide
  have hdisj : listDisjoint (varNames f_is_public_suffix.fn_params)
      (varNames f_is_public_suffix.fn_temps) := by decide
  refine satisfies_internal ge (FunctionEntry2 ge) f_is_public_suffix _ _ (PbodyP c)
    (fun m hp hf hpre hd hag => ?_)
    (ps_body_after ge c acc hcenv hpr hpn hdl1 hdl2 hcl1 hcl2 X)
  let a1 := Mem.alloc m 0 (sizeof ge.genv_cenv (tarray tschar 256))
  let a2 := Mem.alloc a1.1 0 (sizeof ge.genv_cenv (tarray tschar 256))
  have hav : AllocVariables ge.genv_cenv emptyEnv m f_is_public_suffix.fn_vars (envP a1.2 a2.2) a2.1 :=
    .cons _ _ _ _ _ _ _ _ _ rfl (.cons _ _ _ _ _ _ _ _ _ rfl (.nil _ _))
  obtain ⟨hl, hdl, hagl, hloc⟩ := allocVariables_resources hav hnv
    (by
      intro v hv
      simp only [f_is_public_suffix, List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl <;> rw [hcenv] <;> decide)
    (Heap.union hp hf) hag
  have hL : Locs [(a1.2, 256), (a2.2, 256)] hl := by
    have := Case3C.locs_of_localsAt ge.genv_cenv _ _ hl hloc
    rw [hcenv] at this
    exact this
  obtain ⟨dph, dfh⟩ := Heap.disjoint_union_left.mp hdl
  refine ⟨envP a1.2 a2.2,
    PTree.set _domain (.Vptr c.mB c.mO) (PTree.set _co (.Vptr c.coB c.coO)
      (PTree.set _data (.Vptr c.dB c.dO) (createUndefTemps f_is_public_suffix.fn_temps))),
    a2.1, hl, FunctionEntry2.intro hnv hnp hdisj hav rfl,
    Heap.disjoint_union_left.mpr ⟨hd, Heap.disjoint_comm dfh⟩, ?_, ?_⟩
  · rw [Heap.union_assoc, Heap.union_comm (Heap.disjoint_comm dfh), ← Heap.union_assoc]
    exact hagl
  · have hne : a1.2 ≠ a2.2 := by
      obtain ⟨h1, _, d1, rfl, x1, h2, _, d2, rfl, x2, _⟩ := hL
      exact Case3C.anyBytes_ne x1 x2 (by
        rw [Heap.disjoint_union_right] at d1; exact d1.1) (by decide) (by decide)
    refine ⟨(a1.2, a2.2), hne, rfl, ?_, ⟨hp, hl, dph, rfl, hpre.2, hL⟩⟩
    exact TempsHold_cons ((PTree.gss _ _ _))
      (TempsHold_cons ((PTree.gso _ _ _ _ (by decide)).trans (PTree.gss _ _ _))
        (TempsHold_cons ((PTree.gso _ _ _ _ (by decide)).trans ((PTree.gso _ _ _ _ (by decide)).trans
          (PTree.gss _ _ _))) (TempsHold_nil _)))

end Deb2026_8924U
