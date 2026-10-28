/-
CVE-2025-14524: curl 8.14.1 に Debian の CVE-2025-14524.patch を当てたもの（D1）の `Curl_sasl_start`。

証明すること（`start_after`、P1）: 上流（U1）の `Deb2025_14524U.start_after` と同じ形。リダイレクトのあと
（`this_is_a_follow` が 1）で `allow_auth_to_other_hosts` が 0、利用者名があり、`enabledmechs` が EXTERNAL・PLAIN・LOGIN の
ビットを含まないなら、`force_ir` によらず CURLE_OK を返す。`*progress` は 0、`sasl->authused` は 0。
`Curl_auth_create_oauth_bearer_message`・`Curl_auth_create_xoauth_bearer_message` と `sasl->params` には何も与えない。
仕様（`startSpecA`）は U1 と同じものを使う。
-/
import Deb2025_14524DC
open CC CC.Sep CC.HProp
open Deb2025_14524_d1
open Deb2025_14524
open Case5C (addr RR eval_field bitOf)
open Case4debC (lv_field eval_deref_temp)
open Case3C (CellD cellH Cells cell_load3 assign_cell3 Locs)
open Deb2025_14524U (eval_bit2 ldC notbool_nz cast_bool_zero bitOf_true bitOf_false Callee cond_and_false
  msTy brTy Hs argsS startSpecA z64)

set_option maxRecDepth 20000

namespace Deb2025_14524D

/-- 関数の外のセルと、28 番地の単位（`force_ir` を書く前）と、局所変数。 -/
def WD0 (c : Ctx) (bs : Block × Block × Block × Block × Block) : HProp :=
  Cells (outer c c.prv) ∗ (mapsto .Mint32 c.pm c.sB (addr c.sO 28) (.Vint c.sw)
    ∗ Locs (LD bs.1 bs.2.1 bs.2.2.1 bs.2.2.2.1 bs.2.2.2.2))

/-- `force_ir`・`authused`・`*progress` を書いたあと。 -/
def WD1 (c : Ctx) (fir : Bool) (bs : Block × Block × Block × Block × Block) : HProp :=
  Cells (outer c (Integers.Int.repr 0)) ∗ (SW2 c fir (Integers.Int.repr 0)
    ∗ Locs (LD bs.1 bs.2.1 bs.2.2.1 bs.2.2.2.1 bs.2.2.2.2))

def ghTy : List Ty :=
  [tptr (Ty.Tstruct _Curl_easy noattr), tint, tptr (tptr tschar), tptr (tptr tschar), tptr tint]

/-- 呼ばれる側（外部4つ）。仕様は局所変数のブロックについて全称で、どれもメモリの形を保つ。 -/
structure ExtD1 (ge : CGenv) (c : Ctx) (fir : Bool) where
  fdG : FunDef
  gh : Callee ge _Curl_conn_get_host fdG
  tG : typeOfFundef fdG = .Tfunction ghTy tvoid cc_default
  sG : ∀ bs vs, SatisfiesAt ge (FunctionEntry2 ge) fdG
    (specK ghTy tvoid cc_default (WD0 c bs) (WD0 c bs) none) vs
  fdIn : FunDef
  bin : Callee ge _Curl_bufref_init fdIn
  tIn : typeOfFundef fdIn = .Tfunction brTy tvoid cc_default
  sIn : ∀ bs vs, SatisfiesAt ge (FunctionEntry2 ge) fdIn
    (specK brTy tvoid cc_default (WD0 c bs) (WD0 c bs) none) vs
  fdFr : FunDef
  bfr : Callee ge _Curl_bufref_free fdFr
  tFr : typeOfFundef fdFr = .Tfunction brTy tvoid cc_default
  sFr : ∀ bs vs, SatisfiesAt ge (FunctionEntry2 ge) fdFr
    (specK brTy tvoid cc_default (WD1 c fir bs) (WD1 c fir bs) none) vs

abbrev lSD (c : Ctx) (fir : Bool) : List (Ident × Val) :=
  [(_progress, .Vptr c.pB c.pO), (_force_ir, Val.ofBool fir), (_data, .Vptr c.dB c.dO),
   (_sasl, .Vptr c.sB c.sO)]

def envB (bs : Block × Block × Block × Block × Block) : Env :=
  envD bs.1 bs.2.1 bs.2.2.1 bs.2.2.2.1 bs.2.2.2.2

def PbodyD (c : Ctx) (fir : Bool) : Sep.Assn := fun e le hp =>
  ∃ bs : Block × Block × Block × Block × Block,
    ((LD bs.1 bs.2.1 bs.2.2.1 bs.2.2.2.1 bs.2.2.2.2).map Prod.fst).Pairwise (· ≠ ·) ∧
    LocalSt (envB bs) (lSD c fir) (Hs c ∗ Locs (LD bs.1 bs.2.1 bs.2.2.1 bs.2.2.2.1 bs.2.2.2.2)) e le hp

theorem blocks_envB (ge : CGenv) (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (bs : Block × Block × Block × Block × Block) :
    blocksOfEnv ge.genv_cenv (envB bs)
      = [(bs.2.2.2.1, 0, 4), (bs.2.1, 0, 8), (bs.2.2.1, 0, 8), (bs.1, 0, 24), (bs.2.2.2.2, 0, 24)] := by
  rw [hcenv]; rfl

macro "envget" : tactic =>
  `(tactic| (unfold envB envD; repeat (first
      | exact PTree.gss _ _ _
      | exact PTree.gempty _
      | refine (PTree.gso _ _ _ _ (by decide)).trans ?_)))

theorem validC {l : List CellD} {R : HProp} {hp : Heap} {m : Mem} (hH : (Cells l ∗ R) hp)
    (hag : Heap.Agrees hp m) (k : Nat) (hk : k < l.length) {p : Permission} {b : Block}
    {o : Integers.Ptrofs} {v : Val}
    (hl : l[k]'hk = (.Mint8unsigned, p, b, Integers.Ptrofs.unsigned o, v))
    (hpn : permOrder p .Nonempty = true) :
    Mem.weakValidPointer m b (Integers.Ptrofs.unsigned o) = true :=
  cell_valid hl hpn hH hag

theorem boolVal_vint (x : Integers.Int) (m : Mem) :
    Cop.boolVal (.Vint x) tint m = some (!Integers.Int.eq x Integers.Int.zero) := rfl

/-- 条件の値によらず、両方の枝が同じ事後条件を満たす `if`。 -/
theorem if_any (ge fe f) (E : Env) (l : List (Ident × Val)) (H : HProp) (a : Expr) (b : Bool)
    (s1 s2 : Stmt) (R : Sep.ExitConds)
    (hev : ∀ le m hp, TempsHold l le → H hp → Heap.Agrees hp m →
      ∃ v, EvalExpr ge E le m a v ∧ Cop.boolVal v (typeof a) m = some b)
    (h1 : Triple ge fe f (LocalSt E l H) s1 R) (h2 : Triple ge fe f (LocalSt E l H) s2 R) :
    Triple ge fe f (LocalSt E l H) (.Sifthenelse a s1 s2) R :=
  triple_if_local ge fe f E l H a b s1 s2 R hev (by cases b <;> assumption)

set_option maxHeartbeats 40000000 in
theorem start_body_after (ge : CGenv) (c : Ctx) (fir : Bool)
    (hcenv : ge.genv_cenv = prog.prog_comp_env)
    (hpr : permOrder c.pm .Readable = true) (hpn : permOrder c.pm .Nonempty = true)
    (hpw : permOrder c.pm .Writable = true)
    (hfollow : bitOf c.stw 0 = true) (hallow : bitOf c.setw 0 = false)
    (hE : Integers.Int.and (em c) (Integers.Int.repr 32) = Integers.Int.zero)
    (hP : Integers.Int.and (em c) (Integers.Int.repr 2) = Integers.Int.zero)
    (hL : Integers.Int.and (em c) (Integers.Int.repr 1) = Integers.Int.zero)
    (X : ExtD1 ge c fir) :
    Triple ge (FunctionEntry2 ge) f_Curl_sasl_start (PbodyD c fir) f_Curl_sasl_start.fn_body
      (RR (startSpecA c fir).post Sep.Assn.no) := by
  refine Sep.triple_exists ge _ _ _ _ _ (fun bs => ?_)
  refine Case1C.triple_pure ge _ _ _ _ _ _ (fun hnd => ?_)
  refine pre_conv ge _ _ (H2 := WD0 c bs) (fun hp h => by
    unfold WD0 Hs at *; rw [sep_comm_eq (mapsto _ _ _ _ _) (Cells _), sep_assoc_eq] at h; exact h) ?_
  -- result = CURLE_OK; conn = data->conn; mech = NULL; state1 = SASL_STOP; state2 = SASL_FINAL;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envB bs) _ (WD0 c bs) _ _ (.Vint (Integers.Int.repr 0))
      (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envB bs) _ (WD0 c bs) _ _ (.Vptr c.cB c.cO)
      (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_easy)
        (hcenv ▸ off_conn) rfl (ldC hH hag 3 (by simp) rfl hpr))) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envB bs) _ (WD0 c bs) _ _ z64
      (fun _ _ _ _ _ _ => EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envB bs) _ (WD0 c bs) _ _ (.Vint (Integers.Int.repr 0))
      (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_set_local_fwd ge _ _ (envB bs) _ (WD0 c bs) _ _ (.Vint (Integers.Int.repr 17))
      (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _)) ?_
  -- oauth_bearer = (!this_is_a_follow || allow_auth_to_other_hosts) ? str[STRING_BEARER] : NULL;（NULL）
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_seq_fwd ge _ _ _ _ _ _ _
          (triple_set_local_fwd ge _ _ (envB bs) _ (WD0 c bs) _ _
            (.Vint (Cop.bitfieldExtract .I32 .Unsigned 0 1 c.stw))
            (fun le m hp hT hH hag => eval_bit2 (hT.get (by temps_get)) (hcenv ▸ co_easy)
              (hcenv ▸ off_state) (hcenv ▸ co_us) (hcenv ▸ off_follow) (by decide) (by decide)
              (ldC hH hag 7 (by simp) rfl hpr)))
          (triple_if_local ge _ _ (envB bs) _ (WD0 c bs) _ false _ _ _
            (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
              (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))) (notbool_nz (bitOf_true hfollow) m), rfl⟩)
            (triple_seq_fwd ge _ _ _ _ _ _ _
              (triple_set_local_fwd ge _ _ (envB bs) _ (WD0 c bs) _ _
                (.Vint (Cop.bitfieldExtract .I32 .Unsigned 0 1 c.setw))
                (fun le m hp hT hH hag => eval_bit2 (hT.get (by temps_get)) (hcenv ▸ co_easy)
                  (hcenv ▸ off_set) (hcenv ▸ co_ud) (hcenv ▸ off_allow) (by decide) (by decide)
                  (ldC hH hag 5 (by simp) rfl hpr)))
              (triple_set_local_fwd ge _ _ (envB bs) _ (WD0 c bs) _ _ (Val.ofBool false)
                (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
                  (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get)))
                  (cast_bool_zero (bitOf_false hallow) m))))))
        (triple_if_local ge _ _ (envB bs) _ (WD0 c bs) _ false _ _ _
          (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool false) (hT.get (by temps_get)), rfl⟩)
          (triple_set_local_fwd ge _ _ (envB bs) _ (WD0 c bs) _ _ z64
            (fun _ _ _ _ _ _ => EvalExpr.Ecast _ _ _ _
              (EvalExpr.Ecast _ _ _ _ (EvalExpr.Econst_int _ _) rfl) rfl))))
      (triple_set_local_fwd ge _ _ (envB bs) _ (WD0 c bs) _ _ z64
        (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ z64 (hT.get (by temps_get))))) ?_
  -- Curl_conn_get_host(...); Curl_bufref_init(&nullmsg); Curl_bufref_init(&resp);
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (callK_none ge _ _ ghTy tvoid cc_default (WD0 c bs) (WD0 c bs) none _ _ (envB bs) _ _
      X.gh.b X.fdG (X.sG bs) X.gh.fp X.tG rfl
      (fun _ _ _ => eval_callee_global (by envget) X.gh.sym rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ (.Vptr c.dB c.dO) (hT.get (by temps_get))) rfl
        (EvalExprlist.cons _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) rfl
          (EvalExprlist.cons _ _ _ _ _ _ _
            (EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _ (by envget))) rfl
            (EvalExprlist.cons _ _ _ _ _ _ _
              (EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _ (by envget))) rfl
              (EvalExprlist.cons _ _ _ _ _ _ _
                (EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _ (by envget))) rfl
                EvalExprlist.nil)))))) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (callK_none ge _ _ brTy tvoid cc_default (WD0 c bs) (WD0 c bs) none _ _ (envB bs) _ _
      X.bin.b X.fdIn (X.sIn bs) X.bin.fp X.tIn rfl
      (fun _ _ _ => eval_callee_global (by envget) X.bin.sym rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _ (by envget))) rfl EvalExprlist.nil)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (callK_none ge _ _ brTy tvoid cc_default (WD0 c bs) (WD0 c bs) none _ _ (envB bs) _ _
      X.bin.b X.fdIn (X.sIn bs) X.bin.fp X.tIn rfl
      (fun _ _ _ => eval_callee_global (by envget) X.bin.sym rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _ (by envget))) rfl EvalExprlist.nil)) ?_
  -- sasl->force_ir = force_ir; sasl->authused = 0;
  refine pre_conv ge _ _ (H2 := mapsto .Mint32 c.pm c.sB (addr c.sO 28) (.Vint c.sw)
    ∗ (Cells (outer c c.prv) ∗ Locs (LD bs.1 bs.2.1 bs.2.2.1 bs.2.2.2.1 bs.2.2.2.2)))
    (fun hp h => by unfold WD0 at h; rwa [sep_left_comm_eq] at h) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (bitstore_front ge _ _ (envB bs) _ _ c.pm c.sB (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 28))
      18 c.sw (if fir then Integers.Int.one else Integers.Int.zero) _ _ hpw hpr rfl (by decide) (by decide)
      (fun le m hT => EvalLvalue.Efield_struct _ _ _ _ _ _ _ _ _ _
        (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_sasl) (hcenv ▸ off_fir))
      (fun le m hT => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool fir) (hT.get (by temps_get)),
        by cases fir <;> rfl⟩)) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (store16_word ge _ _ (envB bs) _ _ c.pm c.sB (Integers.Ptrofs.add c.sO (Integers.Ptrofs.repr 28))
      (swF c fir) (.Vint (Integers.Int.repr 0)) _ _ hpw rfl
      (fun le m hT => lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_sasl)
        (hcenv ▸ off_au))
      (fun le m hT => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)) ?_
  refine pre_conv ge _ _ (H2 := Cells (outer c c.prv) ∗ (SW2 c fir (Integers.Int.repr 0)
      ∗ Locs (LD bs.1 bs.2.1 bs.2.2.1 bs.2.2.2.1 bs.2.2.2.2)))
    (fun hp h => by
      unfold SW2
      rw [sep_assoc_eq] at h
      rw [sep_left_comm_eq, sep_assoc_eq]
      exact h) ?_
  -- enabledmechs = sasl->authmechs & sasl->prefmech;  *progress = SASL_IDLE;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envB bs) _ _ _ _ (.Vint (Integers.Int.zero_ext 16 c.am))
        (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_sasl)
          (hcenv ▸ off_am) rfl (ldC hH hag 0 (by simp) rfl hpr)))
      (triple_seq_fwd ge _ _ _ _ _ _ _
        (triple_set_local_fwd ge _ _ (envB bs) _ _ _ _ (.Vint (Integers.Int.zero_ext 16 c.pf))
          (fun le m hp hT hH hag => eval_field (hT.get (by temps_get)) (hcenv ▸ co_sasl)
            (hcenv ▸ off_pf) rfl (ldC hH hag 1 (by simp) rfl hpr)))
        (triple_set_local_fwd ge _ _ (envB bs) _ _ _ _ (.Vint (em c))
          (fun le m hp hT _ _ => EvalExpr.Ecast _ _ _ _
            (EvalExpr.Ebinop _ _ _ _ _ _ _
              (EvalExpr.Etempvar _ _ (.Vint (Integers.Int.zero_ext 16 c.am)) (hT.get (by temps_get)))
              (EvalExpr.Etempvar _ _ (.Vint (Integers.Int.zero_ext 16 c.pf)) (hT.get (by temps_get))) rfl)
            rfl)))) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (assign_cell3 ge _ _ (envB bs) _ (outer c c.prv) _ 2 (by simp) .Mint32 c.pm c.pB c.pO
      (.Vint c.prv) (.Vint (Integers.Int.repr 0)) rfl _ _ hpw rfl
      (fun le m hT => EvalLvalue.Ederef _ _ _ _ (EvalExpr.Etempvar _ _ _ (hT.get (by temps_get))))
      (fun _ _ _ _ _ _ => ⟨_, EvalExpr.Econst_int _ _, rfl⟩)) ?_
  refine pre_conv ge _ _ (H2 := WD1 c fir bs) (fun hp h => h) ?_
  -- 方式の選択: EXTERNAL でない、利用者名あり、OAUTHBEARER・XOAUTH2 は Bearer が NULL なので選ばない、PLAIN・LOGIN でない
  refine triple_seq_fwd ge _ _ _ (LocalSt (envB bs) [(_result, .Vint (Integers.Int.repr 0)), (_mech, z64)]
    (WD1 c fir bs)) _ _ _ ?ch ?tail
  case ch =>
    have h5 : Integers.Int.and (em c) (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 5))
        = Integers.Int.zero := hE
    have h1 : Integers.Int.and (em c) (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 1))
        = Integers.Int.zero := hP
    have h0 : Integers.Int.and (em c) (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 0))
        = Integers.Int.zero := hL
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_if_local ge _ _ (envB bs) _ (WD1 c fir bs) _ false _ _ _
        (fun le m hp hT _ _ => ⟨.Vint (Integers.Int.and (em c) (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 5))), EvalExpr.Ebinop _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vint (em c)) (hT.get (by temps_get)))
          (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) (EvalExpr.Econst_int _ _) rfl)
          rfl, cond_and_false _ _ h5 m⟩)
        (triple_set_local_fwd ge _ _ (envB bs) _ (WD1 c fir bs) _ _ (.Vint (Integers.Int.repr 0))
          (fun _ _ _ _ _ _ => EvalExpr.Econst_int _ _))) ?_
    refine triple_if_local ge _ _ (envB bs) _ (WD1 c fir bs) _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (.Vint (Integers.Int.repr 0))
        (hT.get (by temps_get)), rfl⟩) ?_
    rw [if_neg Bool.false_ne_true]
    refine triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_set_local_fwd ge _ _ (envB bs) _ (WD1 c fir bs) _ _ (.Vptr c.uB c.uO)
        (fun le m hp hT hH hag => EvalExpr.Elvalue _ _ _ .Full _
          (lv_field (EvalExpr.Elvalue _ _ _ .Full _
              (lv_field (EvalExpr.Elvalue _ _ _ .Full _
                  (lv_field (eval_deref_temp (hT.get (by temps_get))) rfl (hcenv ▸ co_easy)
                    (hcenv ▸ off_state)) (DerefLoc.copy rfl))
                rfl (hcenv ▸ co_us) (hcenv ▸ off_aptr)) (DerefLoc.copy rfl))
            rfl (hcenv ▸ co_aptr) (hcenv ▸ off_auser))
          (DerefLoc.value Mptr _ rfl (ldC hH hag 6 (by simp) rfl hpr)))) ?_
    refine triple_if_local ge _ _ (envB bs) _ (WD1 c fir bs) _ true _ _ _
      (fun le m hp hT hH hag => ⟨_, EvalExpr.Etempvar _ _ (.Vptr c.uB c.uO) (hT.get (by temps_get)),
        boolVal_ptr _ rfl (validC hH hag 9 (by simp) rfl hpn)⟩) ?_
    rw [if_pos rfl]
    -- OAUTHBEARER: (enabledmechs & OAUTHBEARER) && oauth_bearer（NULL）
    refine triple_seq_fwd ge _ _ _ ?Qo _ _ _ ?o1 ?o2
    case o1 =>
      refine if_any ge _ _ (envB bs) _ (WD1 c fir bs) _
        (!Integers.Int.eq (Integers.Int.and (em c) (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 8)))
          Integers.Int.zero) _ _ _
        (fun le m hp hT _ _ => ⟨.Vint (Integers.Int.and (em c) (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 8))), EvalExpr.Ebinop _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vint (em c)) (hT.get (by temps_get)))
          (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) (EvalExpr.Econst_int _ _) rfl)
          rfl, boolVal_vint _ m⟩) ?_ ?_
      · refine triple_set_local_fwd ge _ _ (envB bs) _ (WD1 c fir bs) _ _ (Val.ofBool false) ?_
        intro le m hp hT _ _
        exact EvalExpr.Ecast _ tbool _ _
            (EvalExpr.Etempvar _oauth_bearer (tptr tschar) z64 (hT.get (by temps_get)))
            (show Cop.semCast z64 (tptr tschar) tbool m = some (Val.ofBool false) from rfl)
      · exact triple_set_local_fwd ge _ _ (envB bs) _ (WD1 c fir bs) _ _ (Val.ofBool false)
          (fun _ _ _ _ _ _ => EvalExpr.Econst_int (Integers.Int.repr 0) tint)
    case o2 =>
    refine triple_if_local ge _ _ (envB bs) _ (WD1 c fir bs) _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool false) (hT.get (by temps_get)), rfl⟩) ?_
    rw [if_neg Bool.false_ne_true]
    -- XOAUTH2: (enabledmechs & XOAUTH2) && oauth_bearer（NULL）
    refine triple_seq_fwd ge _ _ _ ?Qx _ _ _ ?x1 ?x2
    case x1 =>
      refine if_any ge _ _ (envB bs) _ (WD1 c fir bs) _
        (!Integers.Int.eq (Integers.Int.and (em c) (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 7)))
          Integers.Int.zero) _ _ _
        (fun le m hp hT _ _ => ⟨.Vint (Integers.Int.and (em c) (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 7))), EvalExpr.Ebinop _ _ _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vint (em c)) (hT.get (by temps_get)))
          (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) (EvalExpr.Econst_int _ _) rfl)
          rfl, boolVal_vint _ m⟩) ?_ ?_
      · refine triple_set_local_fwd ge _ _ (envB bs) _ (WD1 c fir bs) _ _ (Val.ofBool false) ?_
        intro le m hp hT _ _
        exact EvalExpr.Ecast _ tbool _ _
            (EvalExpr.Etempvar _oauth_bearer (tptr tschar) z64 (hT.get (by temps_get)))
            (show Cop.semCast z64 (tptr tschar) tbool m = some (Val.ofBool false) from rfl)
      · exact triple_set_local_fwd ge _ _ (envB bs) _ (WD1 c fir bs) _ _ (Val.ofBool false)
          (fun _ _ _ _ _ _ => EvalExpr.Econst_int (Integers.Int.repr 0) tint)
    case x2 =>
    refine triple_if_local ge _ _ (envB bs) _ (WD1 c fir bs) _ false _ _ _
      (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool false) (hT.get (by temps_get)), rfl⟩) ?_
    rw [if_neg Bool.false_ne_true]
    -- PLAIN・LOGIN のビットは無い
    refine triple_if_local ge _ _ (envB bs) _ (WD1 c fir bs) _ false _ _ _
      (fun le m hp hT _ _ => ⟨.Vint (Integers.Int.and (em c) (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 1))), EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ (.Vint (em c)) (hT.get (by temps_get)))
        (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) (EvalExpr.Econst_int _ _) rfl)
        rfl, cond_and_false _ _ h1 m⟩) ?_
    rw [if_neg Bool.false_ne_true]
    refine triple_if_local ge _ _ (envB bs) _ (WD1 c fir bs) _ false _ _ _
      (fun le m hp hT _ _ => ⟨.Vint (Integers.Int.and (em c) (Integers.Int.shl (Integers.Int.repr 1) (Integers.Int.repr 0))), EvalExpr.Ebinop _ _ _ _ _ _ _
        (EvalExpr.Etempvar _ _ (.Vint (em c)) (hT.get (by temps_get)))
        (EvalExpr.Ebinop _ _ _ _ _ _ _ (EvalExpr.Econst_int _ _) (EvalExpr.Econst_int _ _) rfl)
        rfl, cond_and_false _ _ h0 m⟩) ?_
    rw [if_neg Bool.false_ne_true]
    exact weaken ge _ _ (triple_skip ge _ _ _) (by subt)
  case tail =>
  -- if(!result && mech) …（mech は NULL）  Curl_bufref_free(&resp);  return result;
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (triple_seq_fwd ge _ _ _ _ _ _ _
      (triple_if_local ge _ _ (envB bs) _ (WD1 c fir bs) _ true _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Eunop _ _ _ _ _
          (EvalExpr.Etempvar _ _ (.Vint (Integers.Int.repr 0)) (hT.get (by temps_get))) rfl, rfl⟩)
        (triple_set_local_fwd ge _ _ (envB bs) _ (WD1 c fir bs) _ _ (Val.ofBool false)
          (fun le m hp hT _ _ => EvalExpr.Ecast _ tbool _ _
            (EvalExpr.Etempvar _mech (tptr tschar) z64 (hT.get (by temps_get)))
            (show Cop.semCast z64 (tptr tschar) tbool m = some (Val.ofBool false) from rfl))))
      (triple_if_local ge _ _ (envB bs) _ (WD1 c fir bs) _ false _ _ _
        (fun le m hp hT _ _ => ⟨_, EvalExpr.Etempvar _ _ (Val.ofBool false) (hT.get (by temps_get)), rfl⟩)
        (triple_skip ge _ _ _))) ?_
  refine triple_seq_fwd ge _ _ _ _ _ _ _
    (callK_none ge _ _ brTy tvoid cc_default (WD1 c fir bs) (WD1 c fir bs) none _ _ (envB bs) _ _
      X.bfr.b X.fdFr (X.sFr bs) X.bfr.fp X.tFr rfl
      (fun _ _ _ => eval_callee_global (by envget) X.bfr.sym rfl)
      (fun le m hT => EvalExprlist.cons _ _ _ _ _ _ _
        (EvalExpr.Eaddrof _ _ _ _ (EvalLvalue.Evar_local _ _ _ (by envget))) rfl EvalExprlist.nil)) ?_
  refine pre_conv ge _ _ (H2 := (Cells (outer c (Integers.Int.repr 0)) ∗ SW2 c fir (Integers.Int.repr 0))
      ∗ Locs (LD bs.1 bs.2.1 bs.2.2.1 bs.2.2.2.1 bs.2.2.2.2))
    (fun hp h => by unfold WD1 at h; rwa [← sep_assoc_eq] at h) ?_
  obtain ⟨b1, b2, b3, b4, b5⟩ := bs
  refine Case3C.ret_locs ge _ _ _ _ _ _ _ (.Vint (Integers.Int.repr 0)) (.Vint (Integers.Int.repr 0)) _
    (fun le m hp hT _ _ => EvalExpr.Etempvar _ _ (.Vint (Integers.Int.repr 0)) (hT.get (by temps_get)))
    (fun _ => rfl) ?_ ?_ (fun hp hH => ⟨rfl, hH⟩)
  · rw [blocks_envB ge hcenv]
    intro x hx'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx'
    rcases hx' with rfl | rfl | rfl | rfl | rfl
    · exact ⟨b4, 4, rfl, by simp⟩
    · exact ⟨b2, 8, rfl, by simp⟩
    · exact ⟨b3, 8, rfl, by simp⟩
    · exact ⟨b1, 24, rfl, by simp⟩
    · exact ⟨b5, 24, rfl, by simp⟩
  · rw [blocks_envB ge hcenv]
    exact pw_reorder hnd

end Deb2025_14524D
